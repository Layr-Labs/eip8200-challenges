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
    (by change 3808 + 3 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3808 + 3 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_entry : Block Artifact.submissionArtifact .Osaka 5614 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4487 121 5614 entryProgram
    (by change 4487 + 121 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 4487 + 121 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_kernel : Block Artifact.submissionArtifact .Osaka 5858 kernelProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4608 1702 5858 kernelProgram
    (by change 4608 + 1702 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 4608 + 1702 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_overflow : Block Artifact.submissionArtifact .Osaka 8128 overflowProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6310 8 8128 overflowProgram
    (by change 6310 + 8 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6310 + 8 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_count : Block Artifact.submissionArtifact .Osaka 8144 countProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6319 4 8144 countProgram
    (by change 6319 + 4 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6319 + 4 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_retain : Block Artifact.submissionArtifact .Osaka 8153 retainProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6324 109 8153 retainProgram
    (by change 6324 + 109 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6324 + 109 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_exit : Block Artifact.submissionArtifact .Osaka 8799 exitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6818 114 8799 exitProgram
    (by change 6818 + 114 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6818 + 114 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_overflowBranch : Block Artifact.submissionArtifact .Osaka 8143 HistoricalSearch.CRTControl.jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6318 1 8143 HistoricalSearch.CRTControl.jumpiProgram
    (by change 6318 + 1 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6318 + 1 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_countBranch : Block Artifact.submissionArtifact .Osaka 8152 HistoricalSearch.CRTControl.jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6323 1 8152 HistoricalSearch.CRTControl.jumpiProgram
    (by change 6323 + 1 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6323 + 1 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_retainBranch : Block Artifact.submissionArtifact .Osaka 8322 HistoricalSearch.CRTControl.jumpProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6433 1 8322 HistoricalSearch.CRTControl.jumpProgram
    (by change 6433 + 1 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6433 + 1 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_exitBranch : Block Artifact.submissionArtifact .Osaka 8975 HistoricalSearch.CRTControl.jumpProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6932 1 8975 HistoricalSearch.CRTControl.jumpProgram
    (by change 6932 + 1 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6932 + 1 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

def block_loopHead : Block Artifact.submissionArtifact .Osaka 5857 HistoricalSearch.CRTControl.jumpDestProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4607 1 5857 HistoricalSearch.CRTControl.jumpDestProgram
    (by change 4607 + 1 ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 4607 + 1 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [CRTSliceFast.locations_map]; rfl)
    (by decide)

theorem pc_3942 : Artifact.submissionArtifact.instructionPC 3096 = 3942 := by
  rw [PCFast.instructionPC_eq_byteLength]
  rfl

theorem validJump3942 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3942 = true := by
  have h := Artifact.isValidJumpDest_index 3096 (by rfl)
  simpa only [Artifact.instructionPC, pc_3942] using h

theorem pc_5615 : Artifact.submissionArtifact.instructionPC 4487 = 5614 := by
  rw [PCFast.instructionPC_eq_byteLength]
  rfl

theorem validJump5615 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5614 = true := by
  have h := Artifact.isValidJumpDest_index 4487 (by rfl)
  simpa only [Artifact.instructionPC, pc_5615] using h

theorem pc_5858 : Artifact.submissionArtifact.instructionPC 4607 = 5857 := by
  rw [PCFast.instructionPC_eq_byteLength]
  rfl

theorem validJump5858 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5857 = true := by
  have h := Artifact.isValidJumpDest_index 4607 (by rfl)
  simpa only [Artifact.instructionPC, pc_5858] using h

theorem pc_8800 : Artifact.submissionArtifact.instructionPC 6818 = 8799 := by
  rw [PCFast.instructionPC_eq_byteLength]
  rfl

theorem validJump8800 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 8799 = true := by
  have h := Artifact.isValidJumpDest_index 6818 (by rfl)
  simpa only [Artifact.instructionPC, pc_8800] using h

end Challenge.Modexp.Submission.Proofs.Fast.CRTArtifactBlocks
