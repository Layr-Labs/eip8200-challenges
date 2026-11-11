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
def counterBlock : Block Artifact.artifact .Osaka 7657 counterHeadProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 5836 5 7657 counterHeadProgram
    (by change 5836 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def counterJumpBlock : Block Artifact.artifact .Osaka 7665 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 5841 1 7665 jumpiProgram
    (by change 5841 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def normalizesquareBlock : Block Artifact.artifact .Osaka 10484 normalizesquareProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8132 4 10484 normalizesquareProgram
    (by change 8132 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump6152 : Decode.isValidJumpDest Artifact.bytecode 5567 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4262
    (show Artifact.instructions[4262]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4262 = 5567 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11008 : Decode.isValidJumpDest Artifact.bytecode 10484 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8132
    (show Artifact.instructions[8132]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8132 = 10484 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.LoopBlocks
