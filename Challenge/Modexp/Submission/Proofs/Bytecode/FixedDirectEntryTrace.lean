import Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectFallbackTrace

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # Redirect from the inherited `BDONE` to the fixed-exponent dispatcher. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectEntryTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
open Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates

def entryPath : List (Challenge.EvmProof.Stepper.Located
    Artifact.submissionArtifact .Osaka) :=
  [opAt 1265 .JUMPDEST, pushAt 1266 2 4057, opAt 1267 .JUMP]

set_option linter.unusedSimpArgs false in
theorem run_entry (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock entryPath
      (Exp.bDone s memory n bsize esize msize) =
      some (entryState s memory n bsize esize msize) := by
  simp (config := { maxSteps := 300000 })
    [entryPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Exp.bDone, entryState, Exp.outer, hcode, hrun,
      FixedDirectPaths.jumpDest4057,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

def gasSteps_entry (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (Exp.bDone s memory n bsize esize msize)
      (entryState s memory n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka entryPath hcode hfork
    (run_entry s memory n bsize esize msize hcode hrun) hrun hnp

set_option linter.unusedSimpArgs false in
theorem run_guard_small (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (he : esize ≤ 3)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.guard
      (entryState s memory n bsize esize msize) =
      some (dispatcherState s memory n bsize esize msize) := by
  have hgt : UInt256.gt (UInt256.ofNat esize) (UInt256.ofNat 3) =
      UInt256.ofNat 0 :=
    gt_ofNat_of_le (Nat.lt_of_le_of_lt he (by norm_num)) (by norm_num) (by omega)
  simp (config := { maxSteps := 300000 })
    [FixedDirectPaths.guard, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      entryState, dispatcherState, Exp.bDone, Exp.outer, hcode, hrun, hgt,
      Exp.not_isTrue_zero, FixedDirectPaths.jumpDest3892,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_guard_large (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hlarge : 3 < esize)
    (he : esize ≤ 1024)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.guard
      (entryState s memory n bsize esize msize) =
      some (FixedDirectStates.fallback s memory n bsize esize msize) := by
  have hgt : UInt256.gt (UInt256.ofNat esize) (UInt256.ofNat 3) =
      UInt256.ofNat 1 :=
    gt_ofNat_of_lt (Nat.lt_of_le_of_lt he (by norm_num))
      (by norm_num) hlarge
  simp (config := { maxSteps := 300000 })
    [FixedDirectPaths.guard, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      entryState, FixedDirectStates.fallback, Exp.bDone, Exp.outer, hcode, hrun,
      hgt, Exp.isTrue_one, FixedDirectPaths.jumpDest4002,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

def gasSteps_guard_small (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (he : esize ≤ 3)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (entryState s memory n bsize esize msize)
      (dispatcherState s memory n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka FixedDirectPaths.guard
    (by simpa [entryState, Artifact.submissionArtifact] using hcode) hfork
    (run_guard_small s memory n bsize esize msize he hcode hrun)
    (by simpa [entryState] using hrun) hnp

def gasSteps_guard_large (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hlarge : 3 < esize)
    (he : esize ≤ 1024)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (entryState s memory n bsize esize msize)
      (FixedDirectStates.fallback s memory n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka FixedDirectPaths.guard
    (by simpa [entryState, Artifact.submissionArtifact] using hcode) hfork
    (run_guard_large s memory n bsize esize msize hlarge he hcode hrun)
    (by simpa [entryState] using hrun) hnp

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectEntryTrace
