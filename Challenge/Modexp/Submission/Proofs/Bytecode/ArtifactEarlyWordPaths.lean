import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactWindowPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_guard : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5225 EarlyWordProgram.guardProgram :=
  WindowTwentyOneSlice.block allWellFormed 3956 20 5225 EarlyWordProgram.guardProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_hit : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5252 EarlyWordProgram.hitProgram :=
  WindowTwentyOneSlice.block allWellFormed 3976 15 5252 EarlyWordProgram.hitProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_miss : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5273 EarlyWordProgram.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 3991 6 5273 EarlyWordProgram.missProgram (by decide) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths submissionArtifact .Osaka where
  guard := earlyWord_guard
  hit := earlyWord_hit
  miss := earlyWord_miss
  helperJump := by exact isValidJumpDest_index 3956 (by rfl)
  missJump := by exact isValidJumpDest_index 3991 (by rfl)
  hitJump := by exact isValidJumpDest_index 3732 (by rfl)
  legacyJump := by exact isValidJumpDest_index 977 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
