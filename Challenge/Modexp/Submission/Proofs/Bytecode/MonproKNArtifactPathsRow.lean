import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowPaths

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNArtifactPathsRow

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof WindowNineBinding

private def entryBlock : Block Artifact.submissionArtifact .Osaka 1939 MonproKNRowPrograms.entryProgram :=
  WindowNineSlice.block Artifact.allWellFormed 1379 34 1939 MonproKNRowPrograms.entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def outBlock : Block Artifact.submissionArtifact .Osaka 1982 MonproKNRowPrograms.outProgram :=
  WindowNineSlice.block Artifact.allWellFormed 1413 10 1982 MonproKNRowPrograms.outProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def stubBlock : Block Artifact.submissionArtifact .Osaka 2003 MonproKNRowPrograms.stubProgram :=
  WindowNineSlice.block Artifact.allWellFormed 1423 3 2003 MonproKNRowPrograms.stubProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def middleBlock : Block Artifact.submissionArtifact .Osaka 2008 MonproKNRowPrograms.midProgram :=
  WindowNineSlice.block Artifact.allWellFormed 1426 51 2008 MonproKNRowPrograms.midProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def tailBlock : Block Artifact.submissionArtifact .Osaka 2435 MonproKNRowPrograms.tailProgram :=
  WindowNineSlice.block Artifact.allWellFormed 1815 26 2435 MonproKNRowPrograms.tailProgram
    (by decide) (by rfl) (by rfl) (by decide)

private def exitBlock : Block Artifact.submissionArtifact .Osaka 2471 MonproKNRowPrograms.exitProgram :=
  WindowNineSlice.block Artifact.allWellFormed 1841 7 2471 MonproKNRowPrograms.exitProgram
    (by decide) (by rfl) (by rfl) (by decide)

private theorem outerJump : Decode.isValidJumpDest Artifact.submissionArtifact.code 1982 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 1413) = true
  exact Artifact.isValidJumpDest_index 1413 (by rfl)

private theorem l1Jump : Decode.isValidJumpDest Artifact.submissionArtifact.code 4070 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 2804) = true
  exact Artifact.isValidJumpDest_index 2804 (by rfl)

private theorem csubJump : Decode.isValidJumpDest Artifact.submissionArtifact.code 2655 = true := by
  change Decode.isValidJumpDest submissionBytecode (Artifact.instructionPC 1915) = true
  exact Artifact.isValidJumpDest_index 1915 (by rfl)

def rowPaths : MonproKNRowPaths.RowPaths Artifact.submissionArtifact .Osaka where
  entry := entryBlock
  out := outBlock
  stub := stubBlock
  middle := middleBlock
  tail := tailBlock
  exit := exitBlock
  outerJump := outerJump
  l1Jump := l1Jump
  csubJump := csubJump

#print axioms rowPaths

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNArtifactPathsRow
