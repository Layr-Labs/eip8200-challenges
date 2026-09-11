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
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2525 WindowTwentyOneEntry.bridgeProgram :=
  WindowTwentyOneSlice.block allWellFormed 1860 3 2525 WindowTwentyOneEntry.bridgeProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_width :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2335 WindowTwentyOneEntry.widthProgram :=
  WindowTwentyOneSlice.block allWellFormed 1714 15 2335 WindowTwentyOneEntry.widthProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_miss :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2355 WindowTwentyOneEntry.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 1729 2 2355 WindowTwentyOneEntry.missProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2359 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 1731 5 2359 WindowTwentyOneEntry.baseProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2366 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 1736 6 2366 WindowTwentyOneEntry.modulusProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_normalize :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2374 WindowTwentyOneEntry.normalizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 1742 8 2374 WindowTwentyOneEntry.normalizeProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_table :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2384 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 1750 92 2384 WindowTwentyOneTableBuild.program
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_init :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2500 WindowTwentyOneInit.program :=
  WindowTwentyOneSlice.block allWellFormed 1842 18 2500 WindowTwentyOneInit.program
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_iteration :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2530 WindowTwentyOneLoop.iterationProgram :=
  WindowTwentyOneSlice.block allWellFormed 1863 438 2530 WindowTwentyOneLoop.iterationProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_finish :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2993 WindowTwentyOneReturn.program :=
  WindowTwentyOneSlice.block allWellFormed 2301 5 2993 WindowTwentyOneReturn.program
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_zeroReturn :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2999 WindowTwentyOneReturn.zeroProgram :=
  WindowTwentyOneSlice.block allWellFormed 2306 7 2999 WindowTwentyOneReturn.zeroProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def nine_emptyReturn :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 3007 WindowTwentyOneReturn.emptyProgram :=
  WindowTwentyOneSlice.block allWellFormed 2313 14 3007 WindowTwentyOneReturn.emptyProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def fermat_prime : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4812 FermatProgram.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 3693 14 4812 FermatProgram.primeProgram (by decide) (by rfl) (by rfl) (by decide)
private def fermat_exponent : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4865 FermatProgram.exponentProgram :=
  WindowTwentyOneSlice.block allWellFormed 3707 9 4865 FermatProgram.exponentProgram (by decide) (by rfl) (by rfl) (by decide)
private def fermat_result : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4877 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 3716 16 4877 FermatProgram.returnProgram (by decide) (by rfl) (by rfl) (by decide)
private def fermat_miss : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4896 FermatProgram.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 3732 4 4896 FermatProgram.missProgram (by decide) (by rfl) (by rfl) (by decide)
def fermatPaths : FermatProgram.Paths submissionArtifact .Osaka where
  prime := fermat_prime
  exponent := fermat_exponent
  result := fermat_result
  miss := fermat_miss
  missJump := by exact isValidJumpDest_index 3732 (by rfl)
  legacyJump := by exact isValidJumpDest_index 1731 (by rfl)

def twentyOnePaths : WindowTwentyOneGasRoute.Paths submissionArtifact .Osaka where
  entryBridge := nine_bridge
  entryJump := by exact isValidJumpDest_index 1714 (by rfl)
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
    have h := isValidJumpDest_index 3693 (by rfl)
    exact h
  emptyJump := by
    have h := isValidJumpDest_index 2313 (by rfl)
    exact h
  zeroJump := by
    have h := isValidJumpDest_index 2306 (by rfl)
    exact h
  loopJump := by
    have h := isValidJumpDest_index 1863 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 415 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
