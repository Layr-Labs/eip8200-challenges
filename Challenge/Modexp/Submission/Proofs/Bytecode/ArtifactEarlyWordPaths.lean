import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactWindowPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_guard : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5251 EarlyWordProgram.guardProgram :=
  WindowTwentyOneSlice.block allWellFormed 3897 20 5251 EarlyWordProgram.guardProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_hit : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5278 EarlyWordProgram.hitProgram :=
  WindowTwentyOneSlice.block allWellFormed 3917 15 5278 EarlyWordProgram.hitProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_miss : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5299 EarlyWordProgram.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 3932 6 5299 EarlyWordProgram.missProgram (by decide) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths submissionArtifact .Osaka where
  guard := earlyWord_guard
  hit := earlyWord_hit
  miss := earlyWord_miss
  helperJump := by exact isValidJumpDest_index 3897 (by rfl)
  missJump := by exact isValidJumpDest_index 3932 (by rfl)
  hitJump := by exact isValidJumpDest_index 3674 (by rfl)
  legacyJump := by exact isValidJumpDest_index 935 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
