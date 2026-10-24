import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PrefixPC
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FixedDirectFallbackTrace

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # Base conversion now returns directly to the fixed-exponent dispatcher. -/

namespace CycleSubmission.Global.FixedDirectEntryTrace
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
open CycleSubmission.Global.FixedDirectPaths

def entryPath : List (Challenge.EvmProof.Stepper.Located
    CycleSubmission.Artifact.artifact .Osaka) :=
  []

set_option linter.unusedSimpArgs false in
theorem run_entry (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock entryPath
      (Exp.bDone s memory n bsize esize msize) =
      some (entryState s memory n bsize esize msize) := by
  simp (config := { maxSteps := 300000 })
    [entryPath, CycleSubmission.Global.Fast.opAt, CycleSubmission.Global.Fast.pushAt, CycleSubmission.Global.Fast.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Exp.bDone, entryState, Exp.outer, hrun,
      FixedDirectPaths.jumpDest3892,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

def gasSteps_entry (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (Exp.bDone s memory n bsize esize msize)
      (entryState s memory n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka entryPath hcode hfork
    (run_entry s memory n bsize esize msize hcode hrun) hrun hnp

end CycleSubmission.Global.FixedDirectEntryTrace
