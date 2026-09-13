import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardBase

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The entry byte gate: `PUSH0 CALLDATALOAD PUSH0 BYTE PUSH2 7 EQ PUSH2 4859 JUMPI`. -/

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

private theorem pc_b1 : Artifact.submissionArtifact.instructionPC 1 = 1 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b2 : Artifact.submissionArtifact.instructionPC 2 = 2 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b3 : Artifact.submissionArtifact.instructionPC 3 = 3 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b4 : Artifact.submissionArtifact.instructionPC 4 = 4 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b5 : Artifact.submissionArtifact.instructionPC 5 = 7 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b6 : Artifact.submissionArtifact.instructionPC 6 = 8 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b7 : Artifact.submissionArtifact.instructionPC 7 = 11 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b0 : Artifact.submissionArtifact.instructionPC 0 = 0 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

theorem guard_dest : Decode.isValidJumpDest submissionBytecode 4859 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3836 = 4859 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3836 (by rfl)
  rwa [hpc] at h

theorem run_byte_prefix (input : ByteArray) :
    run bytePrefix (PatternedScan.stS input 0 []) =
      some (PatternedScan.stS input 11 [4859, byteCondition input]) := by
  let w := MachineState.readWord input 0
  let b := UInt256.byteAt 0 w
  let v := UInt256.eq 7 b
  let l0 : Located := pushAt 0 0 0
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 0 0 [] (by norm_num) pc_b0)
    (PatternedScan.stepS_push0 input 0 [] (by simp) (by norm_num))
  let l1 : Located := opAt 1 .CALLDATALOAD
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 1 1 [0] (by norm_num) pc_b1)
    (PatternedScan.stepS_calldataload input 1 0 [] (by simp) (by norm_num))
  let l2 : Located := pushAt 2 0 0
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 2 2 [w] (by norm_num) pc_b2)
    (PatternedScan.stepS_push0 input 2 [w] (by simp) (by norm_num))
  let l3 : Located := opAt 3 .BYTE
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 3 3 [0, w] (by norm_num) pc_b3)
    (PatternedScan.stepS_byte input 3 0 w [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4 2 7
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4 4 [b] (by norm_num) pc_b4)
    (PatternedScan.stepS_push input 4 2 7 [b] (by simp) (by decide) (by decide) (by norm_num))
  let l5 : Located := opAt 5 .EQ
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 5 7 [7, b] (by norm_num) pc_b5)
    (PatternedScan.stepS_eq input 7 7 b [] (by simp) (by norm_num))
  let l6 : Located := pushAt 6 2 4859
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 6 8 [v] (by norm_num) pc_b6)
    (PatternedScan.stepS_push input 8 2 4859 [v] (by simp) (by decide) (by decide) (by norm_num))
  have hseq1 := DataStepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have hseq2 := DataStepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ hseq1 rfl h2
  have hseq3 := DataStepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ hseq2 rfl h3
  have hseq4 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ hseq3 rfl h4
  have hseq5 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ hseq4 rfl h5
  have hseq6 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ hseq5 rfl h6
  have hv : v = byteCondition input := by
    simp only [v, b, w, byteCondition, Word.literal_eq_ofNat]
  rw [hv] at hseq6
  exact hseq6

theorem run_byte_taken (input : ByteArray) (hbyte : firstByte input = 7) :
    run bytePath (PatternedScan.stS input 0 []) = some (PatternedScan.stS input 4859 []) := by
  have hp := run_byte_prefix input
  rw [byteCondition_one input hbyte] at hp
  have hj : run [opAt 7 .JUMPI]
      (PatternedScan.stS input 11 [4859, UInt256.ofNat 1]) =
      some (PatternedScan.stS input 4859 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 7 11 _ (by norm_num) pc_b7)
      (PatternedScan.stepS_jumpi_taken input 11 4859 4859 (UInt256.ofNat 1) []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _) (by decide) guard_dest)
  exact DataStepper.runLocatedBlock_append bytePrefix [opAt 7 .JUMPI] _ _ _ hp rfl hj

theorem run_byte_fall (input : ByteArray) (hbyte : firstByte input ≠ 7) :
    run bytePath (PatternedScan.stS input 0 []) = some (PatternedScan.stS input 12 []) := by
  have hp := run_byte_prefix input
  rw [byteCondition_zero input hbyte] at hp
  have hj : run [opAt 7 .JUMPI]
      (PatternedScan.stS input 11 [4859, UInt256.ofNat 0]) =
      some (PatternedScan.stS input 12 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 7 11 _ (by norm_num) pc_b7)
      (PatternedScan.stepS_jumpi_fall input 11 4859 (UInt256.ofNat 0) []
        (by simp) (by norm_num) (by decide))
  exact DataStepper.runLocatedBlock_append bytePrefix [opAt 7 .JUMPI] _ _ _ hp rfl hj

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
