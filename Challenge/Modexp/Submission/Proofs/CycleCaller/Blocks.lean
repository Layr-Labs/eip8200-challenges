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
  [.op .JUMPDEST,
   .push 2 2519,
   .push 1 1,
   .op (.Dup ⟨2, by decide⟩),
   .op .SUB,
   .push 2 512,
   .push 2 2112,
   .push 2 3780,
   .push 2 3202,
   .op .JUMP]
def fixedBlock : Block Artifact.artifact .Osaka 2369 fixedProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1858 10 2369 fixedProgram
    (by change 1858 + 10 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def commonProgram : List Instr :=
  [.op .JUMPDEST]
def commonBlock : Block Artifact.artifact .Osaka 3202 commonProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2446 1 3202 commonProgram
    (by change 2446 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def setupBlock : Block Artifact.artifact .Osaka 3203 CycleSubmission.DeadSetup.fullEntryProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2447 33 3203 CycleSubmission.DeadSetup.fullEntryProgram
    (by change 2447 + 33 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def entryProgram : List Instr :=
  [.op .JUMPDEST,
   .push 2 480,
   .op .SUB]
def entryBlock : Block Artifact.artifact .Osaka 3780 entryProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2845 3 3780 entryProgram
    (by change 2845 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
/-- The width test: width 4 jumps to the r5 prologue at 5334, width 8 falls through to the
operand guard. -/
def testProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 128, .op .ADD, .op .ISZERO, .push 2 5334]
def testBlock : Block Artifact.artifact .Osaka 3785 testProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2848 5 3785 testProgram
    (by change 2848 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def branchProgram : List Instr :=
  [.op .JUMPI]
def branchBlock : Block Artifact.artifact .Osaka 3793 branchProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2853 1 3793 branchProgram
    (by change 2853 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
/-- The width-8 operand guard: unless the top 110 bits of the staged operand's leading word at
2368 are all ones, the call jumps to the cycle entry at 5506 (and then `A·2^112 + 2N ≤ R`
holds, so the radix-240 square loop never overflows); otherwise it falls through to the general
route at 219. -/
def guardProgram : List Instr :=
  [.push 2 2368,
   .op .MLOAD,
   .op .NOT,
   .push 1 146,
   .op .SHR,
   .push 2 5527]
def guardBlock : Block Artifact.artifact .Osaka 3794 guardProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2854 6 3794 guardProgram
    (by change 2854 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def guardJumpBlock : Block Artifact.artifact .Osaka 3805 branchProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2860 1 3805 branchProgram
    (by change 2860 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def bailJumpProgram : List Instr :=
  [.push 1 219, .op .JUMP]
def bailJumpBlock : Block Artifact.artifact .Osaka 3806 bailJumpProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2861 2 3806 bailJumpProgram
    (by change 2861 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem valid3181 : Decode.isValidJumpDest Artifact.bytecode 3202 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2446
    (show Artifact.instructions[2446]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2446 = 3202 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid3728 : Decode.isValidJumpDest Artifact.bytecode 3780 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2845
    (show Artifact.instructions[2845]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2845 = 3780 := by
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
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4095
    (show Artifact.instructions[4095]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4095 = 5334 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid5964 : Decode.isValidJumpDest Artifact.bytecode 5527 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4201
    (show Artifact.instructions[4201]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4201 = 5527 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h

end CycleSubmission.CallerBlocks
