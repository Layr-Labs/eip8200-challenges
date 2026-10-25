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
  [.op .JUMPDEST, .push 2 2519, .push 1 1, .op (.Dup ⟨2, by decide⟩), .op .SUB, .push 2 512, .push 2 2112, .push 2 3728, .push 2 3181, .op .JUMP]
def fixedBlock : Block Artifact.artifact .Osaka 2369 fixedProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 1867 10 2369 fixedProgram
    (by change 1867+10 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 1867+10 ≤ 9167)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def commonProgram : List Instr :=
  [.op .JUMPDEST]
def commonBlock : Block Artifact.artifact .Osaka 3181 commonProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2476 1 3181 commonProgram
    (by change 2476+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2476+1 ≤ 9167)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def setupBlock : Block Artifact.artifact .Osaka 3182 TnM128Setup.fullEntryProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2477 54 3182 TnM128Setup.fullEntryProgram
    (by change 2477+54 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2477+54 ≤ 9167)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def entryProgram : List Instr :=
  [.op .JUMPDEST, .push 2 5297, .op (.Swap ⟨1, by decide⟩), .op .POP, .push 1 192, .op .MLOAD, .op (.Swap ⟨2, by decide⟩), .op .POP, .push 2 480, .op .SUB]
def entryBlock : Block Artifact.artifact .Osaka 3728 entryProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2870 10 3728 entryProgram
    (by change 2870+10 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2870+10 ≤ 9167)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def testProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 128, .op .ADD, .push 2 3768]
def testBlock : Block Artifact.artifact .Osaka 3743 testProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2880 4 3743 testProgram
    (by change 2880+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2880+4 ≤ 9167)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def branchProgram : List Instr :=
  [.op .JUMPI]
def branchBlock : Block Artifact.artifact .Osaka 3750 branchProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2884 1 3750 branchProgram
    (by change 2884+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2884+1 ≤ 9167)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def trampolineProgram : List Instr :=
  [.op .JUMPDEST, .push 2 5964]
def trampolineBlock : Block Artifact.artifact .Osaka 3768 trampolineProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2898 2 3768 trampolineProgram
    (by change 2898+2 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2898+2 ≤ 9167)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def jumpProgram : List Instr :=
  [.op .JUMP]
def jumpBlock : Block Artifact.artifact .Osaka 3772 jumpProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2900 1 3772 jumpProgram
    (by change 2900+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 2900+1 ≤ 9167)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem valid3181 : Decode.isValidJumpDest Artifact.bytecode 3181 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2476
    (show Artifact.instructions[2476]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2476 = 3181 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid3728 : Decode.isValidJumpDest Artifact.bytecode 3728 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2870
    (show Artifact.instructions[2870]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2870 = 3728 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid3768 : Decode.isValidJumpDest Artifact.bytecode 3768 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2898
    (show Artifact.instructions[2898]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2898 = 3768 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid5964 : Decode.isValidJumpDest Artifact.bytecode 5964 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4909
    (show Artifact.instructions[4909]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4909 = 5964 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h

end CycleSubmission.CallerBlocks
