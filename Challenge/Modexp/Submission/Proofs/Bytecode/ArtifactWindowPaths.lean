import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.FermatProgram

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private def nine_width :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2187 WindowTwentyOneEntry.widthProgram :=
  WindowTwentyOneSlice.block allWellFormed 1617 15 2187 WindowTwentyOneEntry.widthProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_miss :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2207 WindowTwentyOneEntry.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 1632 2 2207 WindowTwentyOneEntry.missProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2211 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 1634 2 2211 WindowTwentyOneEntry.baseProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2213 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 1636 6 2213 WindowTwentyOneEntry.modulusProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_normalize :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2221 WindowTwentyOneEntry.normalizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 1642 8 2221 WindowTwentyOneEntry.normalizeProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_table :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2231 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 1650 92 2231 WindowTwentyOneTableBuild.program
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_init :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2347 WindowTwentyOneInit.program :=
  WindowTwentyOneSlice.block allWellFormed 1742 18 2347 WindowTwentyOneInit.program
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_iteration :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2372 WindowTwentyOneLoop.iterationProgram :=
  WindowTwentyOneSlice.block allWellFormed 1760 438 2372 WindowTwentyOneLoop.iterationProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_finish :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2835 WindowTwentyOneReturn.program :=
  WindowTwentyOneSlice.block allWellFormed 2198 5 2835 WindowTwentyOneReturn.program
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_zeroReturn :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2841 WindowTwentyOneReturn.zeroProgram :=
  WindowTwentyOneSlice.block allWellFormed 2203 7 2841 WindowTwentyOneReturn.zeroProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def fermat_prime : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4830 FermatProgram.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 3683 14 4830 FermatProgram.primeProgram (by decide) (by rfl) (by rfl) (by decide)
private def fermat_exponent : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4883 FermatProgram.exponentProgram :=
  WindowTwentyOneSlice.block allWellFormed 3697 9 4883 FermatProgram.exponentProgram (by decide) (by rfl) (by rfl) (by decide)
private def fermat_result : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4895 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 3706 16 4895 FermatProgram.returnProgram (by decide) (by rfl) (by rfl) (by decide)
def fermatPaths : FermatProgram.Paths submissionArtifact .Osaka where
  prime := fermat_prime
  exponent := fermat_exponent
  result := fermat_result
  legacyJump := by exact isValidJumpDest_index 1634 (by rfl)

def twentyOnePaths : WindowTwentyOneGasRoute.Paths submissionArtifact .Osaka where
  width := nine_width
  miss := nine_miss
  base := nine_base
  modulus := nine_modulus
  normalize := nine_normalize
  table := nine_table
  init := nine_init
  iteration := nine_iteration
  finish := nine_finish
  zeroReturn := nine_zeroReturn
  hitJump := by
    have h := isValidJumpDest_index 3683 (by rfl)
    exact h
  zeroJump := by
    have h := isValidJumpDest_index 2203 (by rfl)
    exact h
  loopJump := by
    have h := isValidJumpDest_index 1760 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 397 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
