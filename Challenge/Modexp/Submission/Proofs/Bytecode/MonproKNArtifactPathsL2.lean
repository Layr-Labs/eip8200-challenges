import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNLoopPaths

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNArtifactPathsL2

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof WindowNineBinding

private def dispatchBlock : Block Artifact.submissionArtifact .Osaka 2077 MonproKNDispatch.l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 1477 13 2077 MonproKNDispatch.l2Program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy0 : Block Artifact.submissionArtifact .Osaka 2098 MonproKNL2.program :=
  WindowNineSlice.block Artifact.allWellFormed 1490 40 2098 MonproKNL2.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy1 : Block Artifact.submissionArtifact .Osaka 2139 MonproKNL2.program :=
  WindowNineSlice.block Artifact.allWellFormed 1530 40 2139 MonproKNL2.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy2 : Block Artifact.submissionArtifact .Osaka 2180 MonproKNL2.program :=
  WindowNineSlice.block Artifact.allWellFormed 1570 40 2180 MonproKNL2.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy3 : Block Artifact.submissionArtifact .Osaka 2221 MonproKNL2.program :=
  WindowNineSlice.block Artifact.allWellFormed 1610 40 2221 MonproKNL2.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy4 : Block Artifact.submissionArtifact .Osaka 2262 MonproKNL2.program :=
  WindowNineSlice.block Artifact.allWellFormed 1650 40 2262 MonproKNL2.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy5 : Block Artifact.submissionArtifact .Osaka 2303 MonproKNL2.program :=
  WindowNineSlice.block Artifact.allWellFormed 1690 40 2303 MonproKNL2.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy6 : Block Artifact.submissionArtifact .Osaka 2344 MonproKNL2.program :=
  WindowNineSlice.block Artifact.allWellFormed 1730 40 2344 MonproKNL2.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy7 : Block Artifact.submissionArtifact .Osaka 2385 MonproKNL2.program :=
  WindowNineSlice.block Artifact.allWellFormed 1770 40 2385 MonproKNL2.program
    (by decide) (by rfl) (by rfl) (by decide)

private def testBlock : Block Artifact.submissionArtifact .Osaka 2426 MonproKNLoopTests.l2TestProgram :=
  WindowNineSlice.block Artifact.allWellFormed 1810 5 2426 MonproKNLoopTests.l2TestProgram
    (by decide) (by rfl) (by rfl) (by decide)

private theorem jump0 : Decode.isValidJumpDest Artifact.submissionArtifact.code 2098 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 1490) = true
  exact Artifact.isValidJumpDest_index 1490 (by rfl)

private theorem jump1 : Decode.isValidJumpDest Artifact.submissionArtifact.code 2139 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 1530) = true
  exact Artifact.isValidJumpDest_index 1530 (by rfl)

private theorem jump2 : Decode.isValidJumpDest Artifact.submissionArtifact.code 2180 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 1570) = true
  exact Artifact.isValidJumpDest_index 1570 (by rfl)

private theorem jump3 : Decode.isValidJumpDest Artifact.submissionArtifact.code 2221 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 1610) = true
  exact Artifact.isValidJumpDest_index 1610 (by rfl)

private theorem jump4 : Decode.isValidJumpDest Artifact.submissionArtifact.code 2262 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 1650) = true
  exact Artifact.isValidJumpDest_index 1650 (by rfl)

private theorem jump5 : Decode.isValidJumpDest Artifact.submissionArtifact.code 2303 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 1690) = true
  exact Artifact.isValidJumpDest_index 1690 (by rfl)

private theorem jump6 : Decode.isValidJumpDest Artifact.submissionArtifact.code 2344 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 1730) = true
  exact Artifact.isValidJumpDest_index 1730 (by rfl)

private theorem jump7 : Decode.isValidJumpDest Artifact.submissionArtifact.code 2385 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 1770) = true
  exact Artifact.isValidJumpDest_index 1770 (by rfl)

def l2Paths : MonproKNLoopPaths.L2Paths Artifact.submissionArtifact .Osaka where
  dispatch := dispatchBlock
  body := by
    intro slot hslot
    interval_cases slot
    · exact copy0
    · exact copy1
    · exact copy2
    · exact copy3
    · exact copy4
    · exact copy5
    · exact copy6
    · exact copy7
  test := testBlock
  jump := by
    intro slot hslot
    interval_cases slot
    · exact jump0
    · exact jump1
    · exact jump2
    · exact jump3
    · exact jump4
    · exact jump5
    · exact jump6
    · exact jump7

#print axioms l2Paths

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNArtifactPathsL2
