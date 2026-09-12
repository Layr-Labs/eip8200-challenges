import Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic
import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located width-dispatch traces for fixed public exponents

These small blocks isolate the two exponent-width decisions from calldata
loading and from the addition-chain body.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectDispatchTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
open Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

private theorem isTrue_of_xor_ne (x : UInt256) (hx : x ≠ 0) :
    UInt256.isTrue x := by
  unfold UInt256.isTrue
  intro hz
  apply hx
  apply Challenge.EvmProof.Word.word_ext
  change x.toNat = 0
  exact hz

set_option linter.unusedSimpArgs false in
theorem run_entry_three (s : State) (memory : ByteArray)
    (n bsize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock entryPrefix
      (entryState s memory n bsize 3 msize) =
      some (FixedDirectStates.check65537 s memory n bsize 3 msize) := by
  have heq : UInt256.eq (UInt256.ofNat 3) (UInt256.ofNat 3) =
      UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 400000 })
    [entryPrefix, opAt, pushAt, wfOp, jumpBridge3423,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      entryState, Exp.bDone, FixedDirectStates.check65537, Exp.outer,
      hcode, hrun, heq,
      Exp.isTrue_one, jumpDest3895,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_entry_other (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hne : esize ≠ 3) (he : esize ≤ 1024)
    -- With the block ending in a discard rather than a jump, nothing in this proof reads the
    -- code any more; the premise is kept so the call sites keep their arity, and named `_`
    -- because this module sets `warningAsError`, where an unused binder is fatal.
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock entryPrefix
      (entryState s memory n bsize esize msize) =
      some (otherWidth s memory n bsize esize msize) := by
  have heq : UInt256.eq (UInt256.ofNat 3) (UInt256.ofNat esize) =
      UInt256.ofNat 0 := by
    rw [UInt256.eq, Exp.toNat_ofNat_self (by norm_num),
      Exp.toNat_ofNat_self (Nat.lt_of_le_of_lt he (by norm_num)),
      if_neg hne.symm]
  simp (config := { maxSteps := 400000 })
    [entryPrefix, opAt, pushAt, wfOp, jumpBridge3423,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      entryState, Exp.bDone, otherWidth, Exp.outer, hrun, heq,
      Exp.not_isTrue_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_oneWidth_hit (s : State) (memory : ByteArray)
    (n bsize msize : Nat) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock oneWidth
      (otherWidth s memory n bsize 1 msize) =
      some (FixedDirectStates.checkThree s memory n bsize 1 msize) := by
  have hxor : UInt256.xor (UInt256.ofNat 1) (UInt256.ofNat 1) =
      UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 400000 })
    [oneWidth, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      otherWidth, FixedDirectStates.checkThree, Exp.outer, hrun, hxor,
      Exp.not_isTrue_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_oneWidth_miss (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hne : esize ≠ 1) (he : esize ≤ 1024)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock oneWidth
      (otherWidth s memory n bsize esize msize) =
      some (FixedDirectStates.fallback s memory n bsize esize msize) := by
  have helt : esize < 2 ^ 256 := Nat.lt_of_le_of_lt he (by norm_num)
  have hxor : UInt256.xor (UInt256.ofNat 1) (UInt256.ofNat esize) ≠ 0 := by
    intro hx
    have heq' : UInt256.ofNat 1 = UInt256.ofNat esize :=
      (Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic.wordXor_eq_zero_iff
        _ _).mp hx
    have hnat := congrArg UInt256.toNat heq'
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num),
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt helt] at hnat
    exact hne hnat.symm
  have htrue : UInt256.isTrue
      (UInt256.xor (UInt256.ofNat 1) (UInt256.ofNat esize)) :=
    isTrue_of_xor_ne _ hxor
  simp (config := { maxSteps := 400000 })
    [oneWidth, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      otherWidth, FixedDirectStates.fallback, Exp.outer, hcode, hrun, hxor, htrue,
      Exp.isTrue_one, jumpDest3959,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

private def sound {start finish : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path start = some finish)
    (hcode : start.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : start.fork = .Osaka) (hrun : start.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig start.executionEnv.precompileConfig
      start.executionEnv.fork start.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps start finish :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_entry_three (s : State) (memory : ByteArray)
    (n bsize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (entryState s memory n bsize 3 msize)
      (FixedDirectStates.check65537 s memory n bsize 3 msize) :=
  sound entryPrefix
    (run_entry_three s memory n bsize msize hcode hrun)
    (by simpa [entryState, Exp.bDone, Artifact.submissionArtifact] using hcode)
    (by simpa [entryState, Exp.bDone] using hfork)
    (by simpa [entryState, Exp.bDone] using hrun)
    (by simpa [entryState, Exp.bDone] using hnp)

def gasSteps_entry_other (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hne : esize ≠ 3) (he : esize ≤ 1024)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (entryState s memory n bsize esize msize)
      (otherWidth s memory n bsize esize msize) :=
  sound entryPrefix
    (run_entry_other s memory n bsize esize msize hne he hcode hrun)
    (by simpa [entryState, Exp.bDone, Artifact.submissionArtifact] using hcode)
    (by simpa [entryState, Exp.bDone] using hfork)
    (by simpa [entryState, Exp.bDone] using hrun)
    (by simpa [entryState, Exp.bDone] using hnp)

def gasSteps_oneWidth_hit (s : State) (memory : ByteArray)
    (n bsize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (otherWidth s memory n bsize 1 msize)
      (FixedDirectStates.checkThree s memory n bsize 1 msize) :=
  sound oneWidth (run_oneWidth_hit s memory n bsize msize hrun)
    (by simpa [otherWidth, Artifact.submissionArtifact] using hcode)
    (by simpa [otherWidth] using hfork)
    (by simpa [otherWidth] using hrun)
    (by simpa [otherWidth] using hnp)

def gasSteps_oneWidth_miss (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hne : esize ≠ 1) (he : esize ≤ 1024)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (otherWidth s memory n bsize esize msize)
      (FixedDirectStates.fallback s memory n bsize esize msize) :=
  sound oneWidth
    (run_oneWidth_miss s memory n bsize esize msize hne he hcode hrun)
    (by simpa [otherWidth, Artifact.submissionArtifact] using hcode)
    (by simpa [otherWidth] using hfork)
    (by simpa [otherWidth] using hrun)
    (by simpa [otherWidth] using hnp)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectDispatchTrace

#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectDispatchTrace.run_entry_three
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectDispatchTrace.run_entry_other
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectDispatchTrace.run_oneWidth_hit
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectDispatchTrace.run_oneWidth_miss
