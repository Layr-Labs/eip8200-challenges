import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNLoopPaths

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNArtifactPathsL1

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof WindowNineBinding

private def dispatchBlock : Block Artifact.submissionArtifact .Osaka 4070 MonproKNDispatch.l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 2804 13 4070 MonproKNDispatch.l1Program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy0 : Block Artifact.submissionArtifact .Osaka 4089 MonproKNL1.program :=
  WindowNineSlice.block Artifact.allWellFormed 2817 38 4089 MonproKNL1.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy1 : Block Artifact.submissionArtifact .Osaka 4127 MonproKNL1.program :=
  WindowNineSlice.block Artifact.allWellFormed 2855 38 4127 MonproKNL1.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy2 : Block Artifact.submissionArtifact .Osaka 4165 MonproKNL1.program :=
  WindowNineSlice.block Artifact.allWellFormed 2893 38 4165 MonproKNL1.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy3 : Block Artifact.submissionArtifact .Osaka 4203 MonproKNL1.program :=
  WindowNineSlice.block Artifact.allWellFormed 2931 38 4203 MonproKNL1.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy4 : Block Artifact.submissionArtifact .Osaka 4241 MonproKNL1.program :=
  WindowNineSlice.block Artifact.allWellFormed 2969 38 4241 MonproKNL1.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy5 : Block Artifact.submissionArtifact .Osaka 4279 MonproKNL1.program :=
  WindowNineSlice.block Artifact.allWellFormed 3007 38 4279 MonproKNL1.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy6 : Block Artifact.submissionArtifact .Osaka 4317 MonproKNL1.program :=
  WindowNineSlice.block Artifact.allWellFormed 3045 38 4317 MonproKNL1.program
    (by decide) (by rfl) (by rfl) (by decide)

private def copy7 : Block Artifact.submissionArtifact .Osaka 4355 MonproKNL1.program :=
  WindowNineSlice.block Artifact.allWellFormed 3083 38 4355 MonproKNL1.program
    (by decide) (by rfl) (by rfl) (by decide)

private def testBlock : Block Artifact.submissionArtifact .Osaka 4393 MonproKNLoopTests.l1TestProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3121 5 4393 MonproKNLoopTests.l1TestProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def exitBlock : Block Artifact.submissionArtifact .Osaka 4400 MonproKNLoopTests.l1ExitProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3126 2 4400 MonproKNLoopTests.l1ExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

private theorem jump0 : Decode.isValidJumpDest Artifact.submissionArtifact.code 4089 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 2817) = true
  exact Artifact.isValidJumpDest_index 2817 (by rfl)

private theorem jump1 : Decode.isValidJumpDest Artifact.submissionArtifact.code 4127 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 2855) = true
  exact Artifact.isValidJumpDest_index 2855 (by rfl)

private theorem jump2 : Decode.isValidJumpDest Artifact.submissionArtifact.code 4165 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 2893) = true
  exact Artifact.isValidJumpDest_index 2893 (by rfl)

private theorem jump3 : Decode.isValidJumpDest Artifact.submissionArtifact.code 4203 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 2931) = true
  exact Artifact.isValidJumpDest_index 2931 (by rfl)

private theorem jump4 : Decode.isValidJumpDest Artifact.submissionArtifact.code 4241 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 2969) = true
  exact Artifact.isValidJumpDest_index 2969 (by rfl)

private theorem jump5 : Decode.isValidJumpDest Artifact.submissionArtifact.code 4279 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 3007) = true
  exact Artifact.isValidJumpDest_index 3007 (by rfl)

private theorem jump6 : Decode.isValidJumpDest Artifact.submissionArtifact.code 4317 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 3045) = true
  exact Artifact.isValidJumpDest_index 3045 (by rfl)

private theorem jump7 : Decode.isValidJumpDest Artifact.submissionArtifact.code 4355 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 3083) = true
  exact Artifact.isValidJumpDest_index 3083 (by rfl)

private theorem middleJump : Decode.isValidJumpDest Artifact.submissionArtifact.code 2008 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 1426) = true
  exact Artifact.isValidJumpDest_index 1426 (by rfl)

def l1Paths : MonproKNLoopPaths.L1Paths Artifact.submissionArtifact .Osaka where
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
  exit := exitBlock
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
  middle := middleJump

#print axioms l1Paths

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNArtifactPathsL1
