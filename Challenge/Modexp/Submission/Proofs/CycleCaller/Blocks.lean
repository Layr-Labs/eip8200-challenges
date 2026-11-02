import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SetupEntry
import Challenge.Modexp.Submission.Proofs.CycleCaller.DeadSetup
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
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1858 10 2369 fixedProgram
    (by change 1858 + 10 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def commonProgram : List Instr :=
  [.op .JUMPDEST]
def commonBlock : Block Artifact.artifact .Osaka 3181 commonProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2446 1 3181 commonProgram
    (by change 2446 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def setupBlock : Block Artifact.artifact .Osaka 3182 CycleSubmission.DeadSetup.fullEntryProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2447 36 3182 CycleSubmission.DeadSetup.fullEntryProgram
    (by change 2447 + 36 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def entryProgram : List Instr :=
  [.op .JUMPDEST, .push 12 480, .op .SUB]
def entryBlock : Block Artifact.artifact .Osaka 3728 entryProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2848 3 3728 entryProgram
    (by change 2848 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
/-- The width test: width 4 jumps to the r5 prologue at 5334, width 8 falls through to the
operand guard. -/
def testProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 128, .op .ADD, .op .ISZERO, .push 2 5334]
def testBlock : Block Artifact.artifact .Osaka 3743 testProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2851 5 3743 testProgram
    (by change 2851 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def branchProgram : List Instr :=
  [.op .JUMPI]
def branchBlock : Block Artifact.artifact .Osaka 3751 branchProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2856 1 3751 branchProgram
    (by change 2856 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
/-- The width-8 operand guard: unless the top 110 bits of the staged operand's leading word at
2368 are all ones, the call jumps to the cycle entry at 5506 (and then `A·2^112 + 2N ≤ R`
holds, so the radix-240 square loop never overflows); otherwise it falls through to the general
route at 219. -/
def guardProgram : List Instr :=
  [.push 2 2368, .op .MLOAD, .op .NOT, .push 1 146, .op .SHR, .push 2 5506]
def guardBlock : Block Artifact.artifact .Osaka 3752 guardProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2857 6 3752 guardProgram
    (by change 2857 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def guardJumpBlock : Block Artifact.artifact .Osaka 3763 branchProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2863 1 3763 branchProgram
    (by change 2863 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def bailJumpProgram : List Instr :=
  [.push 1 219, .op .JUMP]
def bailJumpBlock : Block Artifact.artifact .Osaka 3764 bailJumpProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2864 2 3764 bailJumpProgram
    (by change 2864 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem valid3181 : Decode.isValidJumpDest Artifact.bytecode 3181 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2446
    (show Artifact.instructions[2446]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2446 = 3181 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid3728 : Decode.isValidJumpDest Artifact.bytecode 3728 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2848
    (show Artifact.instructions[2848]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2848 = 3728 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid219 : Decode.isValidJumpDest Artifact.bytecode 219 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 143
    (show Artifact.instructions[143]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 143 = 219 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid5334 : Decode.isValidJumpDest Artifact.bytecode 5334 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4096
    (show Artifact.instructions[4096]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4096 = 5334 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid5964 : Decode.isValidJumpDest Artifact.bytecode 5506 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4202
    (show Artifact.instructions[4202]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4202 = 5506 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h

end CycleSubmission.CallerBlocks
