import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactWindowPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordSmallExp
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
private def earlyWord_guard : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5256 EarlyWordProgram.guardProgram :=
  WindowTwentyOneSlice.block allWellFormed 3937 20 5256 EarlyWordProgram.guardProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_hit : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5283 EarlyWordProgram.hitProgram :=
  WindowTwentyOneSlice.block allWellFormed 3957 15 5283 EarlyWordProgram.hitProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_miss : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5304 EarlyWordProgram.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 3972 6 5304 EarlyWordProgram.missProgram (by decide) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths submissionArtifact .Osaka where
  guard := earlyWord_guard
  hit := earlyWord_hit
  miss := earlyWord_miss
  helperJump := by exact isValidJumpDest_index 3937 (by rfl)
  missJump := by exact isValidJumpDest_index 3972 (by rfl)
  smallExpJump := by exact isValidJumpDest_index 3978 (by rfl)
  hitJump := by exact isValidJumpDest_index 3703 (by rfl)
  legacyJump := by exact isValidJumpDest_index 935 (by rfl)

private def zeroExp_guard : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5312 EarlyWordSmallExp.zeroExpGuardProgram :=
  WindowTwentyOneSlice.block allWellFormed 3978 11 5312 EarlyWordSmallExp.zeroExpGuardProgram (by decide) (by rfl) (by rfl) (by decide)
private def zeroExp_loadE : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5329 EarlyWordSmallExp.zeroExpLoadEProgram :=
  WindowTwentyOneSlice.block allWellFormed 3989 12 5329 EarlyWordSmallExp.zeroExpLoadEProgram (by decide) (by rfl) (by rfl) (by decide)
private def zeroExp_finish : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5346 EarlyWordSmallExp.zeroExpFinishProgram :=
  WindowTwentyOneSlice.block allWellFormed 4001 20 5346 EarlyWordSmallExp.zeroExpFinishProgram (by decide) (by rfl) (by rfl) (by decide)
def zeroExpPaths : EarlyWordSmallExp.ZeroExpPaths submissionArtifact .Osaka where
  guard := zeroExp_guard
  loadE := zeroExp_loadE
  finish := zeroExp_finish
  missJump := by exact isValidJumpDest_index 3972 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
