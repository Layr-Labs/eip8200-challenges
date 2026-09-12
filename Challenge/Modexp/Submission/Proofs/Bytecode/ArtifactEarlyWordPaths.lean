import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactWindowPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
set_option warningAsError true
set_option maxRecDepth 160000
set_option maxHeartbeats 16000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_guard : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5169 EarlyWordProgram.guardProgram :=
  WindowTwentyOneSlice.block allWellFormed 3907 20 5169 EarlyWordProgram.guardProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_hit : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5196 EarlyWordProgram.hitProgram :=
  WindowTwentyOneSlice.block allWellFormed 3927 15 5196 EarlyWordProgram.hitProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_miss : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5217 EarlyWordProgram.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 3942 6 5217 EarlyWordProgram.missProgram (by decide) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths submissionArtifact .Osaka where
  guard := earlyWord_guard
  hit := earlyWord_hit
  miss := earlyWord_miss
  helperJump := by exact isValidJumpDest_index 3907 (by rfl)
  missJump := by exact isValidJumpDest_index 3942 (by rfl)
  hitJump := by exact isValidJumpDest_index 3680 (by rfl)
  legacyJump := by exact isValidJumpDest_index 858 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
