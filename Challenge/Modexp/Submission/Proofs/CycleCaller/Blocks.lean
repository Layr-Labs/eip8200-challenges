import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SetupEntry
import Challenge.Modexp.Submission.Proofs.CycleCaller.DeadSetup
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 12000000
namespace CycleSubmission.CallerBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
def commonProgram : List Instr :=
 [.op .JUMPDEST, .push 2 512, .push 2 2112, .push 2 3710]
def commonBlock : Block Artifact.artifact .Osaka 3146 commonProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2412 4 3146 commonProgram
    (by change 2412+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def setupBlock : Block Artifact.artifact .Osaka 3156 CycleSubmission.DeadSetup.fullEntryProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2416 34 3156 CycleSubmission.DeadSetup.fullEntryProgram
    (by change 2416+34 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem common_run (s : State) (mem : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
 (hcap : rest.length ≤ 1008) :
 runInstructions commonProgram {s with pc := UInt256.ofNat 3146, memory := mem, stack := [pdst, ret] ++ rest} =
 some {CiosCached.setupState s mem (UInt256.ofNat 3710) 2112 512 pdst ret rest with pc := UInt256.ofNat 3156} := by
 have hc2 : rest.length+2 < 1024 := by omega
 have hc3 : rest.length+3 < 1024 := by omega
 have hc4 : rest.length+4 < 1024 := by omega
 have hc5 : rest.length+5 < 1024 := by omega
 simp [commonProgram, runInstructions, Stepper.runInstr,   CiosCached.setupState, hc2, hc3, hc4, hc5, Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod]

def entryProgram : List Instr :=
  [.op .JUMPDEST,
   .push 2 480,
   .op .SUB]
def entryBlock : Block Artifact.artifact .Osaka 3710 entryProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2806 3 3710 entryProgram
    (by change 2806 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
/-- The width test: width 4 jumps to the r5 prologue at 5334, width 8 falls through to the
operand guard. -/
def testProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 128, .op .ADD, .op .ISZERO, .push 2 5197]
def testBlock : Block Artifact.artifact .Osaka 3715 testProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2809 5 3715 testProgram
    (by change 2809 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def branchProgram : List Instr :=
  [.op .JUMPI]
def branchBlock : Block Artifact.artifact .Osaka 3723 branchProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2814 1 3723 branchProgram
    (by change 2814 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
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
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2815 6 3724 guardProgram
    (by change 2815 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def guardJumpBlock : Block Artifact.artifact .Osaka 3735 branchProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2821 1 3735 branchProgram
    (by change 2821 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def bailJumpProgram : List Instr :=
  [.push 1 207, .op .JUMP]
def bailJumpBlock : Block Artifact.artifact .Osaka 3736 bailJumpProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2822 2 3736 bailJumpProgram
    (by change 2822 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem valid3181 : Decode.isValidJumpDest Artifact.bytecode 3146 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2412
    (show Artifact.instructions[2412]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2412 = 3146 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid3728 : Decode.isValidJumpDest Artifact.bytecode 3710 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 2806
    (show Artifact.instructions[2806]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 2806 = 3710 := by
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
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4029
    (show Artifact.instructions[4029]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4029 = 5197 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem valid5964 : Decode.isValidJumpDest Artifact.bytecode 5383 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 4132
    (show Artifact.instructions[4132]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 4132 = 5383 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h

end CycleSubmission.CallerBlocks
