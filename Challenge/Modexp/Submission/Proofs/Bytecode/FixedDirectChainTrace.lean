import Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectDispatchTrace

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located traces for the fixed-exponent addition chains

The two call blocks end at the kernel entries: every in-place square at
`Exp.sqCall` (the `common` block, `hd = sq_row`), the final product at
`Exp.mpCall` (the kernel's multiply entry).  The remaining control-only blocks
reduce directly.  The loop head additionally stores the square count in memory
word `0x2440 = 9280`, where the kernel's in-kernel square loop reads it.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectChainTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
open Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

set_option linter.unusedSimpArgs false in
theorem run_start (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat) (_hn : 2 ≤ n) (_hn32 : n ≤ 32)
    (_hactive : 298 ≤ s.activeWords.toNat)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.start
      (FixedDirectStates.special s memory n bsize esize msize count) =
      some (FixedDirectStates.square s memory
        n bsize esize msize count) := by
  simp (config := { maxSteps := 300000 })
    [FixedDirectPaths.start, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedDirectStates.special, FixedDirectStates.square, Exp.outer, hrun,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_squareCall (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.squareCall
      (FixedDirectStates.square s memory n bsize esize msize count) =
      some (Exp.sqCall s (Exp.storeWord memory 9280 (UInt256.ofNat count))
        (UInt256.ofNat 3221)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize)) := by
  have haddr : (UInt256.ofNat 9280).toNat = 9280 := by decide
  have hfix : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9280 32) = s.activeWords :=
    Exp.activeWords_fix s 9280 32 (by omega) (by omega) hactive
  simp (config := { maxSteps := 600000 })
    [FixedDirectPaths.squareCall, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedDirectStates.square, Exp.sqCall, Exp.storeWord, Exp.outer,
      hcode, hrun, haddr, hfix,
      FixedDirectPaths.jumpDestSqCommon,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_squareReturn_loop (s : State) (memory : ByteArray)
    (n bsize esize msize k : Nat) (hk : k ≠ 0) (hk16 : k + 1 ≤ 16)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.squareReturn
      (FixedDirectStates.squareReturn s memory n bsize esize msize (k + 1)) =
      some (FixedDirectStates.square s memory n bsize esize msize k) := by
  have hsub : UInt256.ofNat (k + 1) - UInt256.ofNat 1 = UInt256.ofNat k := by
    simpa using Challenge.EvmProof.Word.ofNat_sub_ofNat
      (a := k + 1) (b := 1) (by omega)
      (Nat.lt_of_le_of_lt hk16 (by norm_num))
  have htrue : UInt256.isTrue (UInt256.ofNat k) := by
    show (UInt256.ofNat k).toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hk
  simp (config := { maxSteps := 400000 })
    [FixedDirectPaths.squareReturn, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedDirectStates.squareReturn, FixedDirectStates.square,
      Exp.outer, hcode, hrun, hsub, htrue,
      jumpDest3953, List.exchange,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_squareReturn_exit (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.squareReturn
      (FixedDirectStates.squareReturn s memory n bsize esize msize 1) =
      some (FixedDirectStates.product s memory n bsize esize msize 0) := by
  have hsub : UInt256.ofNat 1 - UInt256.ofNat 1 = UInt256.ofNat 0 := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 300000 })
    [FixedDirectPaths.squareReturn, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedDirectStates.squareReturn, FixedDirectStates.product,
      Exp.outer, hrun, hsub, hfalse, List.exchange,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_product (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.product
      (FixedDirectStates.product s memory n bsize esize msize count) =
      some (Exp.mpCall s memory 2048 1024 1024 (UInt256.ofNat 1571)
        (Exp.outer n bsize esize msize)) := by
  simp (config := { maxSteps := 400000 })
    [FixedDirectPaths.product, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedDirectStates.product, Exp.mpCall, Exp.outer,
      hcode, hrun, FixedDirectPaths.jumpDestSqMulEntry,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_start (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedDirectStates.special s memory n bsize esize msize count)
      (FixedDirectStates.square s memory
        n bsize esize msize count) :=
  sound FixedDirectPaths.start
    (run_start s memory n bsize esize msize count hn hn32 hactive hrun)
    hcode hfork hrun hnp

def gasSteps_squareCall (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedDirectStates.square s memory n bsize esize msize count)
      (Exp.sqCall s (Exp.storeWord memory 9280 (UInt256.ofNat count))
        (UInt256.ofNat 3221)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize)) :=
  sound FixedDirectPaths.squareCall
    (run_squareCall s memory n bsize esize msize count hactive hcode hrun)
    hcode hfork hrun hnp

def gasSteps_squareReturnLoop (s : State) (memory : ByteArray)
    (n bsize esize msize k : Nat) (hk : k ≠ 0) (hk16 : k + 1 ≤ 16)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedDirectStates.squareReturn s memory n bsize esize msize (k + 1))
      (FixedDirectStates.square s memory n bsize esize msize k) :=
  sound FixedDirectPaths.squareReturn
    (run_squareReturn_loop s memory n bsize esize msize k hk hk16 hcode hrun)
    hcode hfork hrun hnp

def gasSteps_squareReturnExit (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedDirectStates.squareReturn s memory n bsize esize msize 1)
      (FixedDirectStates.product s memory n bsize esize msize 0) :=
  sound FixedDirectPaths.squareReturn
    (run_squareReturn_exit s memory n bsize esize msize hrun)
    hcode hfork hrun hnp

def gasSteps_product (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedDirectStates.product s memory n bsize esize msize count)
      (Exp.mpCall s memory 2048 1024 1024 (UInt256.ofNat 1571)
        (Exp.outer n bsize esize msize)) :=
  sound FixedDirectPaths.product
    (run_product s memory n bsize esize msize count hcode hrun)
    hcode hfork hrun hnp

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectChainTrace

#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectChainTrace.run_squareCall
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectChainTrace.run_product
