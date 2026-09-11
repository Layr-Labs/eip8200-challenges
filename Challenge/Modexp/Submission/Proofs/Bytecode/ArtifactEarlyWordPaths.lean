import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactWindowPaths
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
private def earlyWord_smallExpGuard : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5312 EarlyWordSmallExp.smallExpGuardProgram :=
  WindowTwentyOneSlice.block allWellFormed 3978 16 5312 EarlyWordSmallExp.smallExpGuardProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_smallExpLoadE : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5337 EarlyWordSmallExp.smallExpLoadEProgram :=
  WindowTwentyOneSlice.block allWellFormed 3994 15 5337 EarlyWordSmallExp.smallExpLoadEProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_smallExpLoadM : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5358 EarlyWordSmallExp.smallExpLoadMProgram :=
  WindowTwentyOneSlice.block allWellFormed 4009 23 5358 EarlyWordSmallExp.smallExpLoadMProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_smallExpZero : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5389 EarlyWordSmallExp.smallExpZeroProgram :=
  WindowTwentyOneSlice.block allWellFormed 4032 13 5389 EarlyWordSmallExp.smallExpZeroProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_smallExpOne : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5404 EarlyWordSmallExp.smallExpOneProgram :=
  WindowTwentyOneSlice.block allWellFormed 4045 17 5404 EarlyWordSmallExp.smallExpOneProgram (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_smallExpBail5 : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5424 EarlyWordSmallExp.smallExpBail5Program :=
  WindowTwentyOneSlice.block allWellFormed 4062 3 5424 EarlyWordSmallExp.smallExpBail5Program (by decide) (by rfl) (by rfl) (by decide)
private def earlyWord_smallExpBail4 : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5427 EarlyWordSmallExp.smallExpBail4Program :=
  WindowTwentyOneSlice.block allWellFormed 4065 4 5427 EarlyWordSmallExp.smallExpBail4Program (by decide) (by rfl) (by rfl) (by decide)
def earlyWordPaths : EarlyWordProgram.Paths submissionArtifact .Osaka where
  guard := earlyWord_guard
  hit := earlyWord_hit
  miss := earlyWord_miss
  helperJump := by exact isValidJumpDest_index 3937 (by rfl)
  missJump := by exact isValidJumpDest_index 3972 (by rfl)
  hitJump := by exact isValidJumpDest_index 3703 (by rfl)
  legacyJump := by exact isValidJumpDest_index 935 (by rfl)
  smallExpJump := by exact isValidJumpDest_index 3978 (by rfl)

def earlyWordSmallExpPaths : EarlyWordSmallExp.SmallExpPaths submissionArtifact .Osaka where
  guard := earlyWord_smallExpGuard
  loadE := earlyWord_smallExpLoadE
  loadM := earlyWord_smallExpLoadM
  zero := earlyWord_smallExpZero
  one := earlyWord_smallExpOne
  bail5 := earlyWord_smallExpBail5
  bail4 := earlyWord_smallExpBail4
  missJump := by exact isValidJumpDest_index 3972 (by rfl)
  oneJump := by exact isValidJumpDest_index 4045 (by rfl)
  bail5Jump := by exact isValidJumpDest_index 4062 (by rfl)
  bail4Jump := by exact isValidJumpDest_index 4065 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
