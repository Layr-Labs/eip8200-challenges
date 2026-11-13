import Challenge.Modexp.Submission.Proofs.Cycle.Execution.overflowHead
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.counterHead
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.normalizesquare
import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.CRT.CRTControlBase
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 12000000
namespace CycleSubmission.LoopBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open CycleSubmission.Execution
open HistoricalSearch.CRTControl
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowTwentyOneBinding WindowTwentyOneSlice
def counterBlock : Block Artifact.artifact .Osaka 7661 counterHeadProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 5839 5 7661 counterHeadProgram
    (by change 5839 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def counterJumpBlock : Block Artifact.artifact .Osaka 7669 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 5844 1 7669 jumpiProgram
    (by change 5844 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def normalizesquareBlock : Block Artifact.artifact .Osaka 10488 normalizesquareProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8135 4 10488 normalizesquareProgram
    (by change 8135 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump6152 : Decode.isValidJumpDest Artifact.bytecode 5574 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4264
    (show Artifact.instructions[4264]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4264 = 5574 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11008 : Decode.isValidJumpDest Artifact.bytecode 10488 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8135
    (show Artifact.instructions[8135]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8135 = 10488 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.LoopBlocks
