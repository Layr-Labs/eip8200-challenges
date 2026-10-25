import Challenge.Modexp.Submission.Proofs.Cycle.Execution.overflowHead
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.counterHead
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.decrement
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
def overflowBlock : Block Artifact.artifact .Osaka 8077 overflowHeadProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6685 4 8077 overflowHeadProgram
    (by change 6685+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6685+4 ≤ 9187)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def overflowJumpBlock : Block Artifact.artifact .Osaka 8084 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6689 1 8084 jumpiProgram
    (by change 6689+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6689+1 ≤ 9187)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def counterBlock : Block Artifact.artifact .Osaka 8085 counterHeadProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6690 5 8085 counterHeadProgram
    (by change 6690+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6690+5 ≤ 9187)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def counterJumpBlock : Block Artifact.artifact .Osaka 8094 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6695 1 8094 jumpiProgram
    (by change 6695+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6695+1 ≤ 9187)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def decrementBlock : Block Artifact.artifact .Osaka 8095 decrementProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6696 7 8095 decrementProgram
    (by change 6696+7 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6696+7 ≤ 9187)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def repeatJumpBlock : Block Artifact.artifact .Osaka 8109 jumpProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6703 1 8109 jumpProgram
    (by change 6703+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6703+1 ≤ 9187)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def normalizesquareBlock : Block Artifact.artifact .Osaka 11008 normalizesquareProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 9061 4 11008 normalizesquareProgram
    (by change 9061+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 9061+4 ≤ 9187)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump6152 : Decode.isValidJumpDest Artifact.bytecode 6152 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 5029
    (show Artifact.instructions[5029]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 5029 = 6152 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump8110 : Decode.isValidJumpDest Artifact.bytecode 8110 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 6704
    (show Artifact.instructions[6704]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 6704 = 8110 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11008 : Decode.isValidJumpDest Artifact.bytecode 11008 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 9061
    (show Artifact.instructions[9061]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 9061 = 11008 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.LoopBlocks
