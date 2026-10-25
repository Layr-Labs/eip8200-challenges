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
def overflowBlock : Block Artifact.artifact .Osaka 8077 overflowHeadProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6686 4 8077 overflowHeadProgram
    (by change 6686+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6686+4 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def overflowJumpBlock : Block Artifact.artifact .Osaka 8084 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6690 1 8084 jumpiProgram
    (by change 6690+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6690+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def counterBlock : Block Artifact.artifact .Osaka 8085 counterHeadProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6691 9 8085 counterHeadProgram
    (by change 6691+9 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6691+9 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def counterJumpBlock : Block Artifact.artifact .Osaka 8109 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6700 1 8109 jumpiProgram
    (by change 6700+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6700+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def normalizesquareBlock : Block Artifact.artifact .Osaka 11008 normalizesquareProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 9058 4 11008 normalizesquareProgram
    (by change 9058+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 9058+4 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump6152 : Decode.isValidJumpDest Artifact.bytecode 6152 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 5030
    (show Artifact.instructions[5030]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 5030 = 6152 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump8110 : Decode.isValidJumpDest Artifact.bytecode 8110 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 6701
    (show Artifact.instructions[6701]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 6701 = 8110 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11008 : Decode.isValidJumpDest Artifact.bytecode 11008 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 9058
    (show Artifact.instructions[9058]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 9058 = 11008 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.LoopBlocks
