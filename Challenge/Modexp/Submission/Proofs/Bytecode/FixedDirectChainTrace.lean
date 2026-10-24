import Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectDispatchTrace

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located traces for the fixed-exponent addition chains

The two call blocks end at the kernel entries: every in-place square at
`Exp.sqCall` (the `common` block, `hd = sq_row`), the final product at
`Exp.mpCall` (the kernel's multiply entry).  The remaining control-only blocks
reduce directly.  The loop head passes the square count minus one in the kernel
frame's `pdst` slot, which the kernel's in-kernel square loop counts down.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectChainTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
open Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

set_option linter.unusedSimpArgs false in
theorem run_start (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat) (_hn : 2 ≤ n) (_hn32 : n ≤ 8)
    (_hactive : 88 ≤ s.activeWords.toNat)
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
    (n bsize esize msize count : Nat) (hcount : 1 ≤ count) (hcount16 : count ≤ 16)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.squareCall
      (FixedDirectStates.square s memory n bsize esize msize count) =
      some (Exp.sqLoopCall s memory count
        (UInt256.ofNat 2519)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize)) := by
  have hdec : UInt256.ofNat count + UInt256.lnot ({ val := 0 } : UInt256) =
      UInt256.ofNat (count - 1) := by
    interval_cases count <;> decide
  simp (config := { maxSteps := 600000 })
    [FixedDirectPaths.squareCall, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedDirectStates.square, Exp.sqLoopCall, Exp.outer,
      hcode, hrun, hdec,
      FixedDirectPaths.jumpDestSqCommon,
      State.activeWordsAfterUInt256,
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
    (n bsize esize msize count : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hactive : 88 ≤ s.activeWords.toNat)
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
    (n bsize esize msize count : Nat) (hcount : 1 ≤ count) (hcount16 : count ≤ 16)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedDirectStates.square s memory n bsize esize msize count)
      (Exp.sqLoopCall s memory count
        (UInt256.ofNat 2519)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize)) :=
  sound FixedDirectPaths.squareCall
    (run_squareCall s memory n bsize esize msize count hcount hcount16 hcode hrun)
    hcode hfork hrun hnp

#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectChainTrace.run_squareCall
