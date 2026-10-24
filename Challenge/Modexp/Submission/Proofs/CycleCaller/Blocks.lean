import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SetupEntry
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 12000000
namespace CycleSubmission.CallerBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
def fixedProgram : List Instr :=
  [.op .JUMPDEST, .push 2 2519, .push 0 0, .op .NOT, .op (.Dup ⟨2, by decide⟩), .op .ADD, .push 2 512, .push 2 2112, .push 2 3728, .push 2 3181, .op .JUMP]
def fixedBlock : Block Artifact.artifact .Osaka 2369 fixedProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 1867 11 2369 fixedProgram
    (by change 1867+11 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 1867+11 ≤ 9197)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def commonProgram : List Instr :=
  [.op .JUMPDEST]
def commonBlock : Block Artifact.artifact .Osaka 3181 commonProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2478 1 3181 commonProgram
    (by change 2478+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2478+1 ≤ 9197)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def setupBlock : Block Artifact.artifact .Osaka 3182 TnM128Setup.fullEntryProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2479 54 3182 TnM128Setup.fullEntryProgram
    (by change 2479+54 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2479+54 ≤ 9197)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def entryProgram : List Instr :=
  [.op .JUMPDEST, .push 2 5297, .op (.Swap ⟨1, by decide⟩), .op .POP, .push 1 192, .op .MLOAD, .op (.Swap ⟨2, by decide⟩), .op .POP, .push 2 480, .op .SUB]
def entryBlock : Block Artifact.artifact .Osaka 3728 entryProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2881 10 3728 entryProgram
    (by change 2881+10 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2881+10 ≤ 9197)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def testProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 128, .op .ADD, .push 2 3768]
def testBlock : Block Artifact.artifact .Osaka 3743 testProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2891 4 3743 testProgram
    (by change 2891+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2891+4 ≤ 9197)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def branchProgram : List Instr :=
  [.op .JUMPI]
def branchBlock : Block Artifact.artifact .Osaka 3750 branchProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2895 1 3750 branchProgram
    (by change 2895+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2895+1 ≤ 9197)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def trampolineProgram : List Instr :=
  [.op .JUMPDEST, .push 2 5964]
def trampolineBlock : Block Artifact.artifact .Osaka 3768 trampolineProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2909 2 3768 trampolineProgram
    (by change 2909+2 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2909+2 ≤ 9197)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def jumpProgram : List Instr :=
  [.op .JUMP]
def jumpBlock : Block Artifact.artifact .Osaka 3772 jumpProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2911 1 3772 jumpProgram
    (by change 2911+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2911+1 ≤ 9197)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem valid3181 : Decode.isValidJumpDest Artifact.bytecode 3181 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2478
    (show Artifact.instructions[2478]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2478 = 3181 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid3728 : Decode.isValidJumpDest Artifact.bytecode 3728 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2881
    (show Artifact.instructions[2881]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2881 = 3728 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid3768 : Decode.isValidJumpDest Artifact.bytecode 3768 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2909
    (show Artifact.instructions[2909]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2909 = 3768 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid5964 : Decode.isValidJumpDest Artifact.bytecode 5964 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4922
    (show Artifact.instructions[4922]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4922 = 5964 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h

end CycleSubmission.CallerBlocks
