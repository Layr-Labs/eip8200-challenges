import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortSizePrefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EntryGateLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The entry gates: `size != 1000` and the anchor test both jump to the patterned
guard at 4670. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

def guardEntry (input : ByteArray) : State := atPC input 4601

/-- `UInt256.eq` is `if a.toNat = b.toNat then 1 else 0`, and both operands are
below `2 ^ 256`, so the test reduces to the underlying `Nat` comparison. -/
theorem size_eq_zero (input : ByteArray) (k : Nat)
    (hlt : input.size < 2 ^ 256) (hk : k < 2 ^ 256) (hne : input.size ≠ k) :
    UInt256.eq (UInt256.ofNat k) (UInt256.ofNat input.size) = UInt256.ofNat 0 := by
  unfold UInt256.eq
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt]
  simp [Ne.symm hne]

theorem size_eq_one (input : ByteArray) (k : Nat)
    (heq : input.size = k) :
    UInt256.eq (UInt256.ofNat k) (UInt256.ofNat input.size) = UInt256.ofNat 1 := by
  rw [heq]
  unfold UInt256.eq
  simp

def sizePath : List Located := sizePrefix ++ [opAt 10 .JUMPI]
def anchorPath : List Located := anchorPrefix ++ [opAt 18 .JUMPI]

private theorem stepS_calldatasize (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    DataStepper.runInstr (.op .CALLDATASIZE) (PatternedScan.stS input pc stk) =
      some (PatternedScan.stS input (pc + 1) (UInt256.ofNat input.size :: stk)) := by
  unfold DataStepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [PatternedScan.stS, Challenge.Ripemd160.initialState_calldata,
    Challenge.EvmProof.Word.succ_ofNat hpc]

private theorem pc_g6 : Artifact.submissionArtifact.instructionPC 6 = 13 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g7 : Artifact.submissionArtifact.instructionPC 7 = 14 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g8 : Artifact.submissionArtifact.instructionPC 8 = 17 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g9 : Artifact.submissionArtifact.instructionPC 9 = 18 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g10 : Artifact.submissionArtifact.instructionPC 10 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g11 : Artifact.submissionArtifact.instructionPC 11 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g12 : Artifact.submissionArtifact.instructionPC 12 = 23 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g13 : Artifact.submissionArtifact.instructionPC 13 = 24 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g14 : Artifact.submissionArtifact.instructionPC 14 = 26 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g15 : Artifact.submissionArtifact.instructionPC 15 = 27 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g16 : Artifact.submissionArtifact.instructionPC 16 = 29 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g17 : Artifact.submissionArtifact.instructionPC 17 = 30 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g18 : Artifact.submissionArtifact.instructionPC 18 = 33 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

private theorem isValidJumpDest_of_pc (idx pc : Nat)
    (hpc : Artifact.submissionArtifact.instructionPC idx = pc)
    (hget : Artifact.submissionArtifact.instructions[idx]? = some (.op .JUMPDEST)) :
    Decode.isValidJumpDest submissionBytecode pc = true := by
  subst hpc
  exact Artifact.submissionArtifact.isValidJumpDest_index idx hget

theorem generic_dest : Decode.isValidJumpDest submissionBytecode 247 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 156 = 247 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  exact isValidJumpDest_of_pc 156 247 hpc (by rfl)

/-- The size word `1000 - size`. -/
def sizeWord (input : ByteArray) : UInt256 :=
  UInt256.ofNat 1000 - UInt256.ofNat input.size

theorem sizeWord_isTrue (input : ByteArray) (hfit : CalldataFits input)
    (hne : input.size ≠ 1000) : UInt256.isTrue (sizeWord input) := by
  intro hz
  have hz' : (sizeWord input).toNat = 0 := hz
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  rw [sizeWord, Word.word_toNat_sub_cond, Word.word_toNat_ofNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 1000 < 2 ^ 256)] at hz'
  split at hz' <;> omega

theorem sizeWord_false (input : ByteArray) (h : input.size = 1000) :
    ¬ UInt256.isTrue (sizeWord input) := by
  intro ht
  apply ht
  rw [sizeWord, h]
  rfl

theorem run_size_prefix (input : ByteArray) :
    run sizePrefix (PatternedScan.stS input 13 []) =
      some (PatternedScan.stS input 21 [4601, sizeWord input]) := by
  let n := UInt256.ofNat input.size
  let l0 : Located := opAt 6 .CALLDATASIZE
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 6 13 [] (by norm_num) pc_g6)
    (stepS_calldatasize input 13 [] (by simp) (by norm_num))
  let l1 : Located := pushAt 7 2 1000
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 7 14 [n] (by norm_num) pc_g7)
    (PatternedScan.stepS_push input 14 2 1000 [n] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := opAt 8 .SUB
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 8 17 [1000, n] (by norm_num) pc_g8)
    (PatternedScan.stepS_sub input 17 1000 n [] (by simp) (by norm_num))
  let l3 : Located := pushAt 9 2 4601
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 9 18 [1000 - n] (by norm_num) pc_g9)
    (PatternedScan.stepS_push input 18 2 4601 [1000 - n]
      (by simp) (by decide) (by decide) (by norm_num))
  have hseq1 := DataStepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have hseq2 := DataStepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ hseq1 rfl h2
  have hseq3 := DataStepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ hseq2 rfl h3
  exact hseq3

theorem run_size_taken (input : ByteArray) (hfit : CalldataFits input)
    (hne : input.size ≠ 1000) :
    run sizePath (PatternedScan.stS input 13 []) = some (PatternedScan.stS input 4601 []) := by
  have hj : run [opAt 10 .JUMPI]
      (PatternedScan.stS input 21 [4601, sizeWord input]) =
      some (PatternedScan.stS input 4601 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 10 21 _ (by norm_num) pc_g10)
      (PatternedScan.stepS_jumpi_taken input 21 4601 4601 _ []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _)
        (sizeWord_isTrue input hfit hne) guard_dest)
  exact DataStepper.runLocatedBlock_append sizePrefix [opAt 10 .JUMPI] _ _ _
    (run_size_prefix input) rfl hj

theorem run_size_fall (input : ByteArray) (h : input.size = 1000) :
    run sizePath (PatternedScan.stS input 13 []) = some (PatternedScan.stS input 22 []) := by
  have hj : run [opAt 10 .JUMPI]
      (PatternedScan.stS input 21 [4601, sizeWord input]) =
      some (PatternedScan.stS input 22 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 10 21 _ (by norm_num) pc_g10)
      (PatternedScan.stepS_jumpi_fall input 21 4601 _ [] (by simp) (by norm_num)
        (sizeWord_false input h))
  exact DataStepper.runLocatedBlock_append sizePrefix [opAt 10 .JUMPI] _ _ _
    (run_size_prefix input) rfl hj

/-- The anchor word `97 + 255 * calldata[0]`. -/
def anchorWord (input : ByteArray) : UInt256 :=
  UInt256.ofNat 97 + UInt256.ofNat 255 * KnownInputCompactState.referenceWord input

theorem anchorWord_eq (input : ByteArray) : anchorWord input = fullTerm input := by
  rw [anchorWord, fullTerm, Word.word_add_comm]
  congr 1
  exact RawExpressionAC.mul_comm _ _

theorem anchorWord_isTrue (input : ByteArray)
    (hne : KnownInputCompactState.referenceWord input ≠ KnownInputData.fullWord) :
    UInt256.isTrue (anchorWord input) := by
  intro hz
  apply hne
  apply fullTerm_eq_zero input
  rw [← anchorWord_eq]
  exact Word.word_ext hz

theorem anchorWord_false (input : ByteArray)
    (h : KnownInputCompactState.referenceWord input = KnownInputData.fullWord) :
    ¬ UInt256.isTrue (anchorWord input) := by
  intro ht
  apply ht
  rw [anchorWord_eq, fullTerm, h, fullWord_anchor]
  rfl

/-- The recogniser's long-length entry (`JUMPDEST PUSH1 251`). -/
theorem big_dest : Decode.isValidJumpDest submissionBytecode 4793 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3528 = 4793 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  exact isValidJumpDest_of_pc 3528 4793 hpc (by rfl)

theorem run_anchor_prefix (input : ByteArray) :
    run anchorPrefix (PatternedScan.stS input 22 []) =
      some (PatternedScan.stS input 33 [4793, anchorWord input]) := by
  let R := KnownInputCompactState.referenceWord input
  let l0 : Located := pushAt 11 0 0
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 11 22 [] (by norm_num) pc_g11)
    (PatternedScan.stepS_push0 input 22 [] (by simp) (by norm_num))
  let l1 : Located := opAt 12 .CALLDATALOAD
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 12 23 [0] (by norm_num) pc_g12)
    (PatternedScan.stepS_calldataload input 23 0 [] (by simp) (by norm_num))
  let l2 : Located := pushAt 13 1 255
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 13 24 [R] (by norm_num) pc_g13)
    (PatternedScan.stepS_push input 24 1 255 [R] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := opAt 14 .MUL
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 14 26 [255, R] (by norm_num) pc_g14)
    (PatternedScan.stepS_mul input 26 255 R [] (by simp) (by norm_num))
  let l4 : Located := pushAt 15 1 97
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 15 27 [255 * R] (by norm_num) pc_g15)
    (PatternedScan.stepS_push input 27 1 97 [255 * R] (by simp) (by decide) (by decide) (by norm_num))
  let l5 : Located := opAt 16 .ADD
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 16 29 [97, 255 * R] (by norm_num) pc_g16)
    (PatternedScan.stepS_add input 29 97 (255 * R) [] (by simp) (by norm_num))
  let l6 : Located := pushAt 17 2 4793
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 17 30 [97 + 255 * R] (by norm_num) pc_g17)
    (PatternedScan.stepS_push input 30 2 4793 [97 + 255 * R]
      (by simp) (by decide) (by decide) (by norm_num))
  have hseq1 := DataStepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have hseq2 := DataStepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ hseq1 rfl h2
  have hseq3 := DataStepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ hseq2 rfl h3
  have hseq4 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ hseq3 rfl h4
  have hseq5 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ hseq4 rfl h5
  have hseq6 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ hseq5 rfl h6
  exact hseq6

theorem run_anchor_taken (input : ByteArray)
    (hne : KnownInputCompactState.referenceWord input ≠ KnownInputData.fullWord) :
    run anchorPath (PatternedScan.stS input 22 []) = some (PatternedScan.stS input 4793 []) := by
  have hj : run [opAt 18 .JUMPI]
      (PatternedScan.stS input 33 [4793, anchorWord input]) =
      some (PatternedScan.stS input 4793 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 18 33 _ (by norm_num) pc_g18)
      (PatternedScan.stepS_jumpi_taken input 33 4793 4793 _ []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _)
        (anchorWord_isTrue input hne) big_dest)
  exact DataStepper.runLocatedBlock_append anchorPrefix [opAt 18 .JUMPI] _ _ _
    (run_anchor_prefix input) rfl hj

theorem run_anchor_fall (input : ByteArray)
    (h : KnownInputCompactState.referenceWord input = KnownInputData.fullWord) :
    run anchorPath (PatternedScan.stS input 22 []) = some (PatternedScan.stS input 34 []) := by
  have hj : run [opAt 18 .JUMPI]
      (PatternedScan.stS input 33 [4793, anchorWord input]) =
      some (PatternedScan.stS input 34 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 18 33 _ (by norm_num) pc_g18)
      (PatternedScan.stepS_jumpi_fall input 33 4793 _ [] (by simp) (by norm_num)
        (anchorWord_false input h))
  exact DataStepper.runLocatedBlock_append anchorPrefix [opAt 18 .JUMPI] _ _ _
    (run_anchor_prefix input) rfl hj

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
