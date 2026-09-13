import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardBase

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The entry byte gate compares the leading calldata byte with 7. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def firstByte (input : ByteArray) : Nat :=
  (YulSemantics.EVM.byteFrom input.toList 0).toNat

def bytePath : List Located := bytePrefix ++ [opAt 7 .JUMPI]

def byteCondition (input : ByteArray) : UInt256 :=
  UInt256.eq (UInt256.ofNat 7)
    (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0))

theorem firstByte_eq_byteAt (input : ByteArray) :
    UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0) =
      UInt256.ofNat (firstByte input) := by
  simpa [firstByte] using
    (Challenge.EvmProof.Bytes.byteAt_zero_readWord input 0)

theorem firstByte_lt (input : ByteArray) : firstByte input < 256 := by
  unfold firstByte
  exact (YulSemantics.EVM.byteFrom input.toList 0).toNat_lt

theorem byteCondition_zero (input : ByteArray) (hbyte : firstByte input ≠ 7) :
    byteCondition input = UInt256.ofNat 0 := by
  rw [byteCondition, firstByte_eq_byteAt]
  unfold UInt256.eq
  have hlt : firstByte input < 2 ^ 256 :=
    Nat.lt_trans (firstByte_lt input) (by norm_num)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt hlt]
  simp [Ne.symm hbyte]

theorem byteCondition_one (input : ByteArray) (hbyte : firstByte input = 7) :
    byteCondition input = UInt256.ofNat 1 := by
  rw [byteCondition, firstByte_eq_byteAt, hbyte]
  decide

private theorem pc_b1 : Artifact.submissionArtifact.instructionPC 1 = 2 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b2 : Artifact.submissionArtifact.instructionPC 2 = 3 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b3 : Artifact.submissionArtifact.instructionPC 3 = 4 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b4 : Artifact.submissionArtifact.instructionPC 4 = 5 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b5 : Artifact.submissionArtifact.instructionPC 5 = 6 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b6 : Artifact.submissionArtifact.instructionPC 6 = 7 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b7 : Artifact.submissionArtifact.instructionPC 7 = 10 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b0 : Artifact.submissionArtifact.instructionPC 0 = 0 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

theorem guard_dest : Decode.isValidJumpDest submissionBytecode 4872 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3834 = 4872 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3834 (by rfl)
  rwa [hpc] at h

theorem run_byte_prefix (input : ByteArray) :
    run bytePrefix (PatternedScan.stS input 0 []) =
      some (PatternedScan.stS input 10 [4872, byteCondition input]) := by
  have heq (a b : UInt256) : UInt256.eq a b = UInt256.eq b a := by
    simp [UInt256.eq, eq_comm]
  simp (config := {maxSteps := 400000}) [run, bytePrefix, opAt, pushAt, wfOp,
    PatternedScan.stS, initialState, byteCondition,
    pc_b0, pc_b1, pc_b2, pc_b3, pc_b4, pc_b5, pc_b6,
    DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat, heq]

theorem run_byte_taken (input : ByteArray) (hbyte : firstByte input = 7) :
    run bytePath (PatternedScan.stS input 0 []) = some (PatternedScan.stS input 4872 []) := by
  have hp := run_byte_prefix input
  rw [byteCondition_one input hbyte] at hp
  have hj : run [opAt 7 .JUMPI]
      (PatternedScan.stS input 10 [4872, UInt256.ofNat 1]) =
      some (PatternedScan.stS input 4872 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 7 10 _ (by norm_num) pc_b7)
      (PatternedScan.stepS_jumpi_taken input 10 4872 4872 (UInt256.ofNat 1) []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _) (by decide) guard_dest)
  exact DataStepper.runLocatedBlock_append bytePrefix [opAt 7 .JUMPI] _ _ _ hp rfl hj

theorem run_byte_fall (input : ByteArray) (hbyte : firstByte input ≠ 7) :
    run bytePath (PatternedScan.stS input 0 []) = some (PatternedScan.stS input 11 []) := by
  have hp := run_byte_prefix input
  rw [byteCondition_zero input hbyte] at hp
  have hj : run [opAt 7 .JUMPI]
      (PatternedScan.stS input 10 [4872, UInt256.ofNat 0]) =
      some (PatternedScan.stS input 11 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 7 10 _ (by norm_num) pc_b7)
      (PatternedScan.stepS_jumpi_fall input 10 4872 (UInt256.ofNat 0) []
        (by simp) (by norm_num) (by decide))
  exact DataStepper.runLocatedBlock_append bytePrefix [opAt 7 .JUMPI] _ _ _ hp rfl hj

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
