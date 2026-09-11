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
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2216 WindowTwentyOneEntry.widthProgram :=
  WindowTwentyOneSlice.block allWellFormed 1636 15 2216 WindowTwentyOneEntry.widthProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_miss :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2236 WindowTwentyOneEntry.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 1651 2 2236 WindowTwentyOneEntry.missProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2240 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 1653 2 2240 WindowTwentyOneEntry.baseProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2242 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 1655 6 2242 WindowTwentyOneEntry.modulusProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_normalize :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2250 WindowTwentyOneEntry.normalizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 1661 8 2250 WindowTwentyOneEntry.normalizeProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_table :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2260 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 1669 92 2260 WindowTwentyOneTableBuild.program
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_init :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2376 WindowTwentyOneInit.program :=
  WindowTwentyOneSlice.block allWellFormed 1761 18 2376 WindowTwentyOneInit.program
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_iteration :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2401 WindowTwentyOneLoop.iterationProgram :=
  WindowTwentyOneSlice.block allWellFormed 1779 438 2401 WindowTwentyOneLoop.iterationProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_finish :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2864 WindowTwentyOneReturn.program :=
  WindowTwentyOneSlice.block allWellFormed 2217 5 2864 WindowTwentyOneReturn.program
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_zeroReturn :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2870 WindowTwentyOneReturn.zeroProgram :=
  WindowTwentyOneSlice.block allWellFormed 2222 7 2870 WindowTwentyOneReturn.zeroProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def fermat_prime : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4763 FermatProgram.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 3654 14 4763 FermatProgram.primeProgram (by decide) (by rfl) (by rfl) (by decide)
private def fermat_exponent : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4816 FermatProgram.exponentProgram :=
  WindowTwentyOneSlice.block allWellFormed 3668 9 4816 FermatProgram.exponentProgram (by decide) (by rfl) (by rfl) (by decide)
private def fermat_result : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4828 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 3677 16 4828 FermatProgram.returnProgram (by decide) (by rfl) (by rfl) (by decide)
def fermatPaths : FermatProgram.Paths submissionArtifact .Osaka where
  prime := fermat_prime
  exponent := fermat_exponent
  result := fermat_result
  legacyJump := by exact isValidJumpDest_index 1653 (by rfl)

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
    have h := isValidJumpDest_index 3654 (by rfl)
    exact h
  zeroJump := by
    have h := isValidJumpDest_index 2222 (by rfl)
    exact h
  loopJump := by
    have h := isValidJumpDest_index 1779 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 397 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
