import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactWindowPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_guard : WindowTwentyOneBinding.Block submissionArtifact .Osaka 0 EarlyWordProgram.guardProgram :=
  WindowTwentyOneSlice.block allWellFormed 0 19 0 EarlyWordProgram.guardProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_miss : WindowTwentyOneBinding.Block submissionArtifact .Osaka 127 EarlyWordProgram.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 72 3 127 EarlyWordProgram.missProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_resume : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5439 EarlyWordProgram.resumeProgram :=
  WindowTwentyOneSlice.block allWellFormed 4347 5 5439 EarlyWordProgram.resumeProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_zero : WindowTwentyOneBinding.Block submissionArtifact .Osaka 132 EarlyWordProgram.zeroProgram :=
  WindowTwentyOneSlice.block allWellFormed 75 3 132 EarlyWordProgram.zeroProgram (by decide) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths submissionArtifact .Osaka where
  guard := earlyWord_guard
  miss := earlyWord_miss
  resume := earlyWord_resume
  zero := earlyWord_zero
  resumeJump := by exact isValidJumpDest_index 4347 (by rfl)
  missJump := by exact isValidJumpDest_index 72 (by rfl)
  legacyJump := by exact isValidJumpDest_index 423 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
