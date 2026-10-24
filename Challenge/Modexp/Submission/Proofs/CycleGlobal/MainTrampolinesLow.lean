import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ArtifactEarlyWordPaths
import Challenge.Modexp.Submission.Proofs.CycleGlobal.MainDefs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace CycleSubmission.Global.Main
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM

theorem run_tramp0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp0Path
      (initialState CycleSubmission.Artifact.bytecode input 0) = some (trampolineState input 0) := by
  rfl


end CycleSubmission.Global.Main
