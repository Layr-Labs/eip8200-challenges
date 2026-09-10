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

private def nine_bridge :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2613 WindowTwentyOneEntry.bridgeProgram :=
  WindowTwentyOneSlice.block allWellFormed 1909 3 2613 WindowTwentyOneEntry.bridgeProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_width :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2416 WindowTwentyOneEntry.widthProgram :=
  WindowTwentyOneSlice.block allWellFormed 1756 15 2416 WindowTwentyOneEntry.widthProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_miss :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2436 WindowTwentyOneEntry.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 1771 2 2436 WindowTwentyOneEntry.missProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2440 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 1773 5 2440 WindowTwentyOneEntry.baseProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2447 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 1778 6 2447 WindowTwentyOneEntry.modulusProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_normalize :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2455 WindowTwentyOneEntry.normalizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 1784 8 2455 WindowTwentyOneEntry.normalizeProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_table :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2465 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 1792 92 2465 WindowTwentyOneTableBuild.program
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_init :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2581 WindowTwentyOneInit.program :=
  WindowTwentyOneSlice.block allWellFormed 1884 18 2581 WindowTwentyOneInit.program
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_iteration :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2618 WindowTwentyOneLoop.iterationProgram :=
  WindowTwentyOneSlice.block allWellFormed 1912 438 2618 WindowTwentyOneLoop.iterationProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_finish :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 3081 WindowTwentyOneReturn.program :=
  WindowTwentyOneSlice.block allWellFormed 2350 5 3081 WindowTwentyOneReturn.program
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_zeroReturn :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 3087 WindowTwentyOneReturn.zeroProgram :=
  WindowTwentyOneSlice.block allWellFormed 2355 7 3087 WindowTwentyOneReturn.zeroProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_emptyReturn :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 3095 WindowTwentyOneReturn.emptyProgram :=
  WindowTwentyOneSlice.block allWellFormed 2362 14 3095 WindowTwentyOneReturn.emptyProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def fermat_prime : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4869 FermatProgram.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 3720 14 4869 FermatProgram.primeProgram (by decide) (by rfl) (by rfl) (by decide)
private def fermat_exponent : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4922 FermatProgram.exponentProgram :=
  WindowTwentyOneSlice.block allWellFormed 3734 9 4922 FermatProgram.exponentProgram (by decide) (by rfl) (by rfl) (by decide)
private def fermat_result : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4934 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 3743 16 4934 FermatProgram.returnProgram (by decide) (by rfl) (by rfl) (by decide)
private def fermat_miss : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4953 FermatProgram.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 3759 4 4953 FermatProgram.missProgram (by decide) (by rfl) (by rfl) (by decide)
def fermatPaths : FermatProgram.Paths submissionArtifact .Osaka where
  prime := fermat_prime
  exponent := fermat_exponent
  result := fermat_result
  miss := fermat_miss
  missJump := by exact isValidJumpDest_index 3759 (by rfl)
  legacyJump := by exact isValidJumpDest_index 1773 (by rfl)

def twentyOnePaths : WindowTwentyOneGasRoute.Paths submissionArtifact .Osaka where
  entryBridge := nine_bridge
  entryJump := by exact isValidJumpDest_index 1756 (by rfl)
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
  emptyReturn := nine_emptyReturn
  hitJump := by
    have h := isValidJumpDest_index 3720 (by rfl)
    exact h
  emptyJump := by
    have h := isValidJumpDest_index 2362 (by rfl)
    exact h
  zeroJump := by
    have h := isValidJumpDest_index 2355 (by rfl)
    exact h
  loopJump := by
    have h := isValidJumpDest_index 1912 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 415 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
