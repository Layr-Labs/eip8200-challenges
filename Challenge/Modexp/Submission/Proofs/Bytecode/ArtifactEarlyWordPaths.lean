import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactWindowPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_guard : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5115 EarlyWordProgram.guardProgram :=
  WindowTwentyOneSlice.block allWellFormed 3871 20 5115 EarlyWordProgram.guardProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_hit : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5142 EarlyWordProgram.hitProgram :=
  WindowTwentyOneSlice.block allWellFormed 3891 15 5142 EarlyWordProgram.hitProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_miss : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5163 EarlyWordProgram.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 3906 6 5163 EarlyWordProgram.missProgram (by decide) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths submissionArtifact .Osaka where
  guard := earlyWord_guard
  hit := earlyWord_hit
  miss := earlyWord_miss
  helperJump := by exact isValidJumpDest_index 3871 (by rfl)
  missJump := by exact isValidJumpDest_index 3906 (by rfl)
  hitJump := by exact isValidJumpDest_index 3642 (by rfl)
  legacyJump := by exact isValidJumpDest_index 860 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
