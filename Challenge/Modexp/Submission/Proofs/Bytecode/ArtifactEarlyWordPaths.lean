import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_size : WindowTwentyOneBinding.Block submissionArtifact .Osaka 0 EarlyWordProgram.sizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 0 11 0 EarlyWordProgram.sizeProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_width : WindowTwentyOneBinding.Block submissionArtifact .Osaka 16 EarlyWordProgram.widthTestProgram :=
  WindowTwentyOneSlice.block allWellFormed 11 6 16 EarlyWordProgram.widthTestProgram (by decide) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths submissionArtifact .Osaka where
  size := earlyWord_size
  width := earlyWord_width
  legacyJump := by exact isValidJumpDest_index 423 (by rfl)
  genJump := by exact isValidJumpDest_index 52 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
