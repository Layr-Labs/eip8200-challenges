import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactWindowPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_guard : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5241 EarlyWordProgram.guardProgram :=
  WindowTwentyOneSlice.block allWellFormed 3896 20 5241 EarlyWordProgram.guardProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_hit : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5268 EarlyWordProgram.hitProgram :=
  WindowTwentyOneSlice.block allWellFormed 3916 15 5268 EarlyWordProgram.hitProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_miss : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5289 EarlyWordProgram.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 3931 6 5289 EarlyWordProgram.missProgram (by decide) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths submissionArtifact .Osaka where
  guard := earlyWord_guard
  hit := earlyWord_hit
  miss := earlyWord_miss
  helperJump := by exact isValidJumpDest_index 3896 (by rfl)
  missJump := by exact isValidJumpDest_index 3931 (by rfl)
  hitJump := by exact isValidJumpDest_index 3673 (by rfl)
  legacyJump := by exact isValidJumpDest_index 935 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
