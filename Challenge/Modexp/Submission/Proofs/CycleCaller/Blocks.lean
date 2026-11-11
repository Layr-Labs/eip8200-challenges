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
   .push 0 0,
   .push 3 1,
   .op (.Dup ⟨2, by decide⟩),
   .op .SUB,
   .push 2 512,
   .push 2 2112,
   .push 2 3710,
   .push 2 3146,
   .op .JUMP]
def fixedBlock : Block Artifact.artifact .Osaka 2336 fixedProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1845 10 2336 fixedProgram
    (by change 1845 + 10 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def commonProgram : List Instr :=
  [.op .JUMPDEST]
def commonBlock : Block Artifact.artifact .Osaka 3146 commonProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2405 1 3146 commonProgram
    (by change 2405 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def setupBlock : Block Artifact.artifact .Osaka 3147 CycleSubmission.DeadSetup.fullEntryProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2406 33 3147 CycleSubmission.DeadSetup.fullEntryProgram
    (by change 2406 + 33 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def entryProgram : List Instr :=
  [.op .JUMPDEST,
   .push 2 480,
   .op .SUB]
def entryBlock : Block Artifact.artifact .Osaka 3710 entryProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2795 3 3710 entryProgram
    (by change 2795 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
/-- The width test: width 4 jumps to the r5 prologue at 5334, width 8 falls through to the
operand guard. -/
def testProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 128, .op .ADD, .op .ISZERO, .push 2 5197]
def testBlock : Block Artifact.artifact .Osaka 3715 testProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2798 5 3715 testProgram
    (by change 2798 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def branchProgram : List Instr :=
  [.op .JUMPI]
def branchBlock : Block Artifact.artifact .Osaka 3723 branchProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2803 1 3723 branchProgram
    (by change 2803 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
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
   .push 2 5383]
def guardBlock : Block Artifact.artifact .Osaka 3724 guardProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2804 6 3724 guardProgram
    (by change 2804 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def guardJumpBlock : Block Artifact.artifact .Osaka 3735 branchProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2810 1 3735 branchProgram
    (by change 2810 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def bailJumpProgram : List Instr :=
  [.push 1 207, .op .JUMP]
def bailJumpBlock : Block Artifact.artifact .Osaka 3736 bailJumpProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2811 2 3736 bailJumpProgram
    (by change 2811 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem valid3181 : Decode.isValidJumpDest Artifact.bytecode 3146 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2405
    (show Artifact.instructions[2405]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2405 = 3146 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid3728 : Decode.isValidJumpDest Artifact.bytecode 3710 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2795
    (show Artifact.instructions[2795]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2795 = 3710 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid219 : Decode.isValidJumpDest Artifact.bytecode 207 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 135
    (show Artifact.instructions[135]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 135 = 207 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid5334 : Decode.isValidJumpDest Artifact.bytecode 5197 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4018
    (show Artifact.instructions[4018]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4018 = 5197 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid5964 : Decode.isValidJumpDest Artifact.bytecode 5383 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4121
    (show Artifact.instructions[4121]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4121 = 5383 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h

end CycleSubmission.CallerBlocks
