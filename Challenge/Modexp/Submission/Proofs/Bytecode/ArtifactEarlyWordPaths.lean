import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactWindowPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_guard : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5178 EarlyWordProgram.guardProgram :=
  WindowTwentyOneSlice.block allWellFormed 3912 20 5178 EarlyWordProgram.guardProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_hit : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5205 EarlyWordProgram.hitProgram :=
  WindowTwentyOneSlice.block allWellFormed 3932 15 5205 EarlyWordProgram.hitProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_miss : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5226 EarlyWordProgram.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 3947 6 5226 EarlyWordProgram.missProgram (by decide) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths submissionArtifact .Osaka where
  guard := earlyWord_guard
  hit := earlyWord_hit
  miss := earlyWord_miss
  helperJump := by exact isValidJumpDest_index 3912 (by rfl)
  missJump := by exact isValidJumpDest_index 3947 (by rfl)
  hitJump := by exact isValidJumpDest_index 3683 (by rfl)
  legacyJump := by exact isValidJumpDest_index 860 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
