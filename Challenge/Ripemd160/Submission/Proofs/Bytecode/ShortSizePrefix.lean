import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardBase

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The entry byte gate: `PUSH0 CALLDATALOAD PUSH1 251 SHR ISZERO PUSH2 4681 JUMPI`,
taken exactly when the first calldata byte is below 8. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def firstByte (input : ByteArray) : Nat :=
  (YulSemantics.EVM.byteFrom input.toList 0).toNat

def bytePath : List Located := bytePrefix ++ [opAt 12 .JUMPI]

def byteCondition (input : ByteArray) : UInt256 :=
  UInt256.isZero (UInt256.shiftRight (MachineState.readWord input 0) (UInt256.ofNat 251))

theorem firstByte_eq_byteAt (input : ByteArray) :
    UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0) =
      UInt256.ofNat (firstByte input) := by
  simpa [firstByte] using
    (Challenge.EvmProof.Bytes.byteAt_zero_readWord input 0)

theorem firstByte_lt (input : ByteArray) : firstByte input < 256 := by
  unfold firstByte
  exact (YulSemantics.EVM.byteFrom input.toList 0).toNat_lt

/-- The top five bits of the first word are the first byte divided by 8. -/
theorem shift251_toNat (input : ByteArray) :
    (UInt256.shiftRight (MachineState.readWord input 0) (UInt256.ofNat 251)).toNat =
      firstByte input / 8 := by
  have h := Challenge.EvmProof.Bytes.shiftRight_readWord input 0 1 (by norm_num) (by norm_num)
  have h2 := congrArg UInt256.toNat h
  rw [Word.shiftRight_toNat _ (by norm_num), Word.word_toNat_ofNat] at h2
  have hb : Precompile.bytesToNatPadded input 0 1 = firstByte input := by
    rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
    simp [firstByte]
  rw [hb, Nat.mod_eq_of_lt (Nat.lt_trans (firstByte_lt input) (by norm_num))] at h2
  rw [Word.shiftRight_toNat _ (by norm_num),
    show (251 : Nat) = (32 - 1) * 8 + 3 by norm_num, Nat.shiftRight_add, h2,
    Nat.shiftRight_eq_div_pow]

theorem byteCondition_toNat (input : ByteArray) :
    (byteCondition input).toNat = if firstByte input < 8 then 1 else 0 := by
  rw [byteCondition, Word.word_toNat_isZero, shift251_toNat]
  by_cases h : firstByte input < 8
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem byteCondition_true (input : ByteArray) (hbyte : firstByte input < 8) :
    UInt256.isTrue (byteCondition input) := by
  intro hz
  have h := byteCondition_toNat input
  rw [if_pos hbyte] at h
  have hz' : (byteCondition input).toNat = 0 := hz
  omega

theorem byteCondition_false (input : ByteArray) (hbyte : ¬ firstByte input < 8) :
    ¬ UInt256.isTrue (byteCondition input) := by
  intro ht
  apply ht
  have h := byteCondition_toNat input
  rw [if_neg hbyte] at h
  exact h

private theorem stepS_iszero' (input : ByteArray) (pc : Nat) (a : UInt256)
    (rest : List UInt256) (hlen : rest.length + 1 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    DataStepper.runInstr (.op .ISZERO) (PatternedScan.stS input pc (a :: rest)) =
      some (PatternedScan.stS input (pc + 1) (UInt256.isZero a :: rest)) := by
  unfold DataStepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [PatternedScan.stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_lt (input : ByteArray) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    DataStepper.runInstr (.op .LT) (PatternedScan.stS input pc (a :: b :: rest)) =
      some (PatternedScan.stS input (pc + 1) (UInt256.lt a b :: rest)) := by
  unfold DataStepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [PatternedScan.stS, Challenge.EvmProof.Word.succ_ofNat hpc]

private theorem pc_b0 : Artifact.submissionArtifact.instructionPC 6 = 9 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b1 : Artifact.submissionArtifact.instructionPC 7 = 10 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b2 : Artifact.submissionArtifact.instructionPC 8 = 11 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b3 : Artifact.submissionArtifact.instructionPC 9 = 13 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b4 : Artifact.submissionArtifact.instructionPC 10 = 14 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b5 : Artifact.submissionArtifact.instructionPC 11 = 15 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_b6 : Artifact.submissionArtifact.instructionPC 12 = 18 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

theorem guard_dest : Decode.isValidJumpDest submissionBytecode 4681 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3519 = 4681 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3519 (by rfl)
  rwa [hpc] at h

theorem run_byte_prefix (input : ByteArray) :
    run bytePrefix (PatternedScan.stS input 9 []) =
      some (PatternedScan.stS input 18 [4681, byteCondition input]) := by
  let w := MachineState.readWord input 0
  let t := UInt256.shiftRight w 251
  let l0 : Located := pushAt 6 0 0
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 6 9 [] (by norm_num) pc_b0)
    (PatternedScan.stepS_push0 input 9 [] (by simp) (by norm_num))
  let l1 : Located := opAt 7 .CALLDATALOAD
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 7 10 [0] (by norm_num) pc_b1)
    (PatternedScan.stepS_calldataload input 10 0 [] (by simp) (by norm_num))
  let l2 : Located := pushAt 8 1 251
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 8 11 [w] (by norm_num) pc_b2)
    (PatternedScan.stepS_push input 11 1 251 [w] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := opAt 9 .SHR
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 9 13 [251, w] (by norm_num) pc_b3)
    (PatternedScan.stepS_shr input 13 251 w [] (by simp) (by norm_num))
  let l4 : Located := opAt 10 .ISZERO
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 10 14 [t] (by norm_num) pc_b4)
    (stepS_iszero' input 14 t [] (by simp) (by norm_num))
  let l5 : Located := pushAt 11 2 4681
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 11 15 [UInt256.isZero t] (by norm_num) pc_b5)
    (PatternedScan.stepS_push input 15 2 4681 [UInt256.isZero t]
      (by simp) (by decide) (by decide) (by norm_num))
  have hseq1 := DataStepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have hseq2 := DataStepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ hseq1 rfl h2
  have hseq3 := DataStepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ hseq2 rfl h3
  have hseq4 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ hseq3 rfl h4
  have hseq5 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ hseq4 rfl h5
  exact hseq5

theorem run_byte_taken (input : ByteArray) (hbyte : firstByte input < 8) :
    run bytePath (PatternedScan.stS input 9 []) = some (PatternedScan.stS input 4681 []) := by
  have hj : run [opAt 12 .JUMPI]
      (PatternedScan.stS input 18 [4681, byteCondition input]) =
      some (PatternedScan.stS input 4681 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 12 18 _ (by norm_num) pc_b6)
      (PatternedScan.stepS_jumpi_taken input 18 4681 4681 _ []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _)
        (byteCondition_true input hbyte) guard_dest)
  exact DataStepper.runLocatedBlock_append bytePrefix [opAt 12 .JUMPI] _ _ _
    (run_byte_prefix input) rfl hj

theorem run_byte_fall (input : ByteArray) (hbyte : ¬ firstByte input < 8) :
    run bytePath (PatternedScan.stS input 9 []) = some (PatternedScan.stS input 19 []) := by
  have hj : run [opAt 12 .JUMPI]
      (PatternedScan.stS input 18 [4681, byteCondition input]) =
      some (PatternedScan.stS input 19 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 12 18 _ (by norm_num) pc_b6)
      (PatternedScan.stepS_jumpi_fall input 18 4681 _ []
        (by simp) (by norm_num) (byteCondition_false input hbyte))
  exact DataStepper.runLocatedBlock_append bytePrefix [opAt 12 .JUMPI] _ _ _
    (run_byte_prefix input) rfl hj

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
