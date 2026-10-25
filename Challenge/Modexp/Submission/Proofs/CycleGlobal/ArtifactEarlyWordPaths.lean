import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
noncomputable section
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace CycleSubmission.Global.Paths
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_size : WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 0 EarlyWordProgram.sizeProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 0 11 0 EarlyWordProgram.sizeProgram
    (by exact Nat.le_trans (by decide : 0+11 ≤ 9167) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl) (by rfl) (by decide)
private def earlyWord_width : WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 16 EarlyWordProgram.widthTestProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 11 6 16 EarlyWordProgram.widthTestProgram
    (by exact Nat.le_trans (by decide : 11+6 ≤ 9167) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths CycleSubmission.Artifact.artifact .Osaka where
  size := earlyWord_size
  width := earlyWord_width
  legacyJump := by exact CycleSubmission.Global.Binding.jumpDest 404 (by rfl)
  genJump := by exact CycleSubmission.Global.Binding.jumpDest 47 (by rfl)

end CycleSubmission.Global.Paths
