import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactWindowPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_guard : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4951 EarlyWordProgram.guardProgram :=
  WindowTwentyOneSlice.block allWellFormed 3769 20 4951 EarlyWordProgram.guardProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_hit : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4978 EarlyWordProgram.hitProgram :=
  WindowTwentyOneSlice.block allWellFormed 3789 15 4978 EarlyWordProgram.hitProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_miss : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4999 EarlyWordProgram.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 3804 6 4999 EarlyWordProgram.missProgram (by decide) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths submissionArtifact .Osaka where
  guard := earlyWord_guard
  hit := earlyWord_hit
  miss := earlyWord_miss
  helperJump := by exact isValidJumpDest_index 3769 (by rfl)
  missJump := by exact isValidJumpDest_index 3804 (by rfl)
  hitJump := by exact isValidJumpDest_index 3695 (by rfl)
  legacyJump := by exact isValidJumpDest_index 935 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
