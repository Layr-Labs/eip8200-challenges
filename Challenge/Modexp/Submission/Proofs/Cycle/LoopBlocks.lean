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
def counterBlock : Block Artifact.artifact .Osaka 7619 counterHeadProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 5984 5 7619 counterHeadProgram
    (by change 5984+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 5984+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def counterJumpBlock : Block Artifact.artifact .Osaka 7651 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 5989 1 7651 jumpiProgram
    (by change 5989+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 5989+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def normalizesquareBlock : Block Artifact.artifact .Osaka 10550 normalizesquareProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8314 4 10550 normalizesquareProgram
    (by change 8314+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8314+4 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump6152 : Decode.isValidJumpDest Artifact.bytecode 5694 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4360
    (show Artifact.instructions[4360]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4360 = 5694 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11008 : Decode.isValidJumpDest Artifact.bytecode 10550 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8314
    (show Artifact.instructions[8314]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8314 = 10550 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.LoopBlocks
