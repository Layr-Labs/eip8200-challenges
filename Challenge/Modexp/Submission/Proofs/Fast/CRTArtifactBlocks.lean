import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.CRT.CRTKernelExecution
import Challenge.Modexp.Submission.Proofs.CRT.CRTControlBase
import Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace Challenge.Modexp.Submission.Proofs.Fast.CRTArtifactBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowTwentyOneSlice
open HistoricalSearch.GeneratedColumns

def block_hook : Block Artifact.submissionArtifact .Osaka 4816 HistoricalSearch.CRTControl.hookProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3808 3 4816 HistoricalSearch.CRTControl.hookProgram
    (by change 3808 + 3 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3808 + 3 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_entry : Block Artifact.submissionArtifact .Osaka 5615 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4488 121 5615 entryProgram
    (by change 4488 + 121 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 4488 + 121 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_kernel : Block Artifact.submissionArtifact .Osaka 5859 kernelProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4609 2006 5859 kernelProgram
    (by change 4609 + 2006 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 4609 + 2006 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_overflow : Block Artifact.submissionArtifact .Osaka 8507 overflowProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6615 8 8507 overflowProgram
    (by change 6615 + 8 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6615 + 8 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_count : Block Artifact.submissionArtifact .Osaka 8523 countProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6624 4 8523 countProgram
    (by change 6624 + 4 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6624 + 4 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_retain : Block Artifact.submissionArtifact .Osaka 8532 retainProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6629 117 8532 retainProgram
    (by change 6629 + 117 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6629 + 117 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_exit : Block Artifact.submissionArtifact .Osaka 8800 exitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6819 121 8800 exitProgram
    (by change 6819 + 121 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6819 + 121 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_overflowBranch : Block Artifact.submissionArtifact .Osaka 8522 HistoricalSearch.CRTControl.jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6623 1 8522 HistoricalSearch.CRTControl.jumpiProgram
    (by change 6623 + 1 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6623 + 1 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_countBranch : Block Artifact.submissionArtifact .Osaka 8531 HistoricalSearch.CRTControl.jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6628 1 8531 HistoricalSearch.CRTControl.jumpiProgram
    (by change 6628 + 1 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6628 + 1 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_retainBranch : Block Artifact.submissionArtifact .Osaka 8725 HistoricalSearch.CRTControl.jumpProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6746 1 8725 HistoricalSearch.CRTControl.jumpProgram
    (by change 6746 + 1 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6746 + 1 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_exitBranch : Block Artifact.submissionArtifact .Osaka 8997 HistoricalSearch.CRTControl.jumpProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6940 1 8997 HistoricalSearch.CRTControl.jumpProgram
    (by change 6940 + 1 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6940 + 1 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_loopHead : Block Artifact.submissionArtifact .Osaka 5858 HistoricalSearch.CRTControl.jumpDestProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4608 1 5858 HistoricalSearch.CRTControl.jumpDestProgram
    (by change 4608 + 1 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 4608 + 1 ≤ 8722) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

theorem pc_3942 : Artifact.submissionArtifact.instructionPC 3096 = 3942 := by
  rw [PCFast.instructionPC_eq_byteLength]
  rfl

theorem validJump3942 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3942 = true := by
  have h := Artifact.isValidJumpDest_index 3096 (by rfl)
  simpa only [Artifact.instructionPC, pc_3942] using h

theorem pc_5615 : Artifact.submissionArtifact.instructionPC 4488 = 5615 := by
  rw [PCFast.instructionPC_eq_byteLength]
  rfl

theorem validJump5615 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5615 = true := by
  have h := Artifact.isValidJumpDest_index 4488 (by rfl)
  simpa only [Artifact.instructionPC, pc_5615] using h

theorem pc_5858 : Artifact.submissionArtifact.instructionPC 4608 = 5858 := by
  rw [PCFast.instructionPC_eq_byteLength]
  rfl

theorem validJump5858 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5858 = true := by
  have h := Artifact.isValidJumpDest_index 4608 (by rfl)
  simpa only [Artifact.instructionPC, pc_5858] using h

theorem pc_8800 : Artifact.submissionArtifact.instructionPC 6819 = 8800 := by
  rw [PCFast.instructionPC_eq_byteLength]
  rfl

theorem validJump8800 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 8800 = true := by
  have h := Artifact.isValidJumpDest_index 6819 (by rfl)
  simpa only [Artifact.instructionPC, pc_8800] using h

end Challenge.Modexp.Submission.Proofs.Fast.CRTArtifactBlocks
