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
def overflowBlock : Block Artifact.artifact .Osaka 7619 overflowHeadProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6048 4 7619 overflowHeadProgram
    (by change 6048+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6048+4 ≤ 8535)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def overflowJumpBlock : Block Artifact.artifact .Osaka 7626 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6052 1 7626 jumpiProgram
    (by change 6052+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6052+1 ≤ 8535)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def counterBlock : Block Artifact.artifact .Osaka 7627 counterHeadProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6053 6 7627 counterHeadProgram
    (by change 6053+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6053+6 ≤ 8535)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def counterJumpBlock : Block Artifact.artifact .Osaka 7651 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6059 1 7651 jumpiProgram
    (by change 6059+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6059+1 ≤ 8535)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def normalizesquareBlock : Block Artifact.artifact .Osaka 10550 normalizesquareProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8409 4 10550 normalizesquareProgram
    (by change 8409+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8409+4 ≤ 8535)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump6152 : Decode.isValidJumpDest Artifact.bytecode 5694 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4392
    (show Artifact.instructions[4392]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4392 = 5694 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11008 : Decode.isValidJumpDest Artifact.bytecode 10550 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8409
    (show Artifact.instructions[8409]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8409 = 10550 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.LoopBlocks
