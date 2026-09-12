import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactWindowPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_guard : WindowTwentyOneBinding.Block submissionArtifact .Osaka 0 EarlyWordProgram.guardProgram :=
  WindowTwentyOneSlice.block allWellFormed 0 19 0 EarlyWordProgram.guardProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_hit : WindowTwentyOneBinding.Block submissionArtifact .Osaka 26 EarlyWordProgram.hitProgram :=
  WindowTwentyOneSlice.block allWellFormed 19 15 26 EarlyWordProgram.hitProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_miss : WindowTwentyOneBinding.Block submissionArtifact .Osaka 47 EarlyWordProgram.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 34 6 47 EarlyWordProgram.missProgram (by decide) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths submissionArtifact .Osaka where
  guard := earlyWord_guard
  hit := earlyWord_hit
  miss := earlyWord_miss
  missJump := by exact isValidJumpDest_index 34 (by rfl)
  hitJump := by exact isValidJumpDest_index 3834 (by rfl)
  legacyJump := by exact isValidJumpDest_index 895 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
