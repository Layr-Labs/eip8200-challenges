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

def entryPath : List (Challenge.EvmProof.Stepper.Located
    Artifact.submissionArtifact .Osaka) :=
  [opAt 1248 .JUMPDEST,
   pushAt 1249 2 3618,
   opAt 1250 .JUMP]

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
      FixedDirectPaths.jumpDest3892,
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

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectEntryTrace
