import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortSizePrefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EntryGateLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The calldata-size guard: `size < 4` jumps to the patterned guard at 4681. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

def guardEntry (input : ByteArray) : State := atPC input 4681

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

def guardPath : List Located := guardPrefix ++ [opAt 17 .JUMPI]
def sizePath : List Located := sizePrefix ++ [opAt 22 .JUMPI, entryDest]
def sizeFallPath : List Located := sizePrefix ++ [opAt 22 .JUMPI]

private theorem stepS_calldatasize (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    DataStepper.runInstr (.op .CALLDATASIZE) (PatternedScan.stS input pc stk) =
      some (PatternedScan.stS input (pc + 1) (UInt256.ofNat input.size :: stk)) := by
  unfold DataStepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [PatternedScan.stS, Challenge.Ripemd160.initialState_calldata,
    Challenge.EvmProof.Word.succ_ofNat hpc]

private theorem pc_g13 : Artifact.submissionArtifact.instructionPC 13 = 19 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g14 : Artifact.submissionArtifact.instructionPC 14 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g15 : Artifact.submissionArtifact.instructionPC 15 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g16 : Artifact.submissionArtifact.instructionPC 16 = 23 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g17 : Artifact.submissionArtifact.instructionPC 17 = 26 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g18 : Artifact.submissionArtifact.instructionPC 18 = 27 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g19 : Artifact.submissionArtifact.instructionPC 19 = 28 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g20 : Artifact.submissionArtifact.instructionPC 20 = 31 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g21 : Artifact.submissionArtifact.instructionPC 21 = 32 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g22 : Artifact.submissionArtifact.instructionPC 22 = 36 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

theorem generic_dest : Decode.isValidJumpDest submissionBytecode 246 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 147 = 246 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have h := Artifact.submissionArtifact.isValidJumpDest_index 147 (by rfl)
  rwa [hpc] at h

/-- The guard word `size < 4`. -/
def guardWord (input : ByteArray) : UInt256 :=
  UInt256.lt (UInt256.ofNat input.size) (UInt256.ofNat 4)

theorem guardWord_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (guardWord input).toNat = if input.size < 4 then 1 else 0 := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  rw [guardWord, Word.word_toNat_lt, Word.word_toNat_ofNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 4 < 2 ^ 256)]

theorem run_guard_prefix (input : ByteArray) :
    run guardPrefix (PatternedScan.stS input 19 []) =
      some (PatternedScan.stS input 26 [4681, guardWord input]) := by
  let n := UInt256.ofNat input.size
  let l0 : Located := pushAt 13 1 4
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 13 19 [] (by norm_num) pc_g13)
    (PatternedScan.stepS_push input 19 1 4 [] (by simp) (by decide) (by decide) (by norm_num))
  let l1 : Located := opAt 14 .CALLDATASIZE
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 14 21 [4] (by norm_num) pc_g14)
    (stepS_calldatasize input 21 [4] (by simp) (by norm_num))
  let l2 : Located := opAt 15 .LT
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 15 22 [n, 4] (by norm_num) pc_g15)
    (stepS_lt input 22 n 4 [] (by simp) (by norm_num))
  let l3 : Located := pushAt 16 2 4681
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 16 23 [UInt256.lt n 4] (by norm_num) pc_g16)
    (PatternedScan.stepS_push input 23 2 4681 [UInt256.lt n 4]
      (by simp) (by decide) (by decide) (by norm_num))
  have hseq1 := DataStepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have hseq2 := DataStepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ hseq1 rfl h2
  have hseq3 := DataStepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ hseq2 rfl h3
  exact hseq3

theorem run_guard_taken (input : ByteArray) (hfit : CalldataFits input)
    (hsmall : input.size < 4) :
    run guardPath (PatternedScan.stS input 19 []) = some (PatternedScan.stS input 4681 []) := by
  have htrue : UInt256.isTrue (guardWord input) := by
    intro hz
    have h := guardWord_toNat input hfit
    rw [if_pos hsmall] at h
    have hz' : (guardWord input).toNat = 0 := hz
    omega
  have hj : run [opAt 17 .JUMPI]
      (PatternedScan.stS input 26 [4681, guardWord input]) =
      some (PatternedScan.stS input 4681 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 17 26 _ (by norm_num) pc_g17)
      (PatternedScan.stepS_jumpi_taken input 26 4681 4681 _ []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _) htrue guard_dest)
  exact DataStepper.runLocatedBlock_append guardPrefix [opAt 17 .JUMPI] _ _ _
    (run_guard_prefix input) rfl hj

theorem run_guard_fall (input : ByteArray) (hfit : CalldataFits input)
    (h4 : 4 ≤ input.size) :
    run guardPath (PatternedScan.stS input 19 []) = some (PatternedScan.stS input 27 []) := by
  have hfalse : ¬ UInt256.isTrue (guardWord input) := by
    intro ht
    apply ht
    have h := guardWord_toNat input hfit
    rw [if_neg (by omega)] at h
    exact h
  have hj : run [opAt 17 .JUMPI]
      (PatternedScan.stS input 26 [4681, guardWord input]) =
      some (PatternedScan.stS input 27 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 17 26 _ (by norm_num) pc_g17)
      (PatternedScan.stepS_jumpi_fall input 26 4681 _ [] (by simp) (by norm_num) hfalse)
  exact DataStepper.runLocatedBlock_append guardPrefix [opAt 17 .JUMPI] _ _ _
    (run_guard_prefix input) rfl hj

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
    run sizePrefix (PatternedScan.stS input 27 []) =
      some (PatternedScan.stS input 36 [246, sizeWord input]) := by
  let n := UInt256.ofNat input.size
  let l0 : Located := opAt 18 .CALLDATASIZE
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 18 27 [] (by norm_num) pc_g18)
    (stepS_calldatasize input 27 [] (by simp) (by norm_num))
  let l1 : Located := pushAt 19 2 1000
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 19 28 [n] (by norm_num) pc_g19)
    (PatternedScan.stepS_push input 28 2 1000 [n] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := opAt 20 .SUB
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 20 31 [1000, n] (by norm_num) pc_g20)
    (PatternedScan.stepS_sub input 31 1000 n [] (by simp) (by norm_num))
  let l3 : Located := pushAt 21 3 246
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 21 32 [1000 - n] (by norm_num) pc_g21)
    (PatternedScan.stepS_push input 32 3 246 [1000 - n]
      (by simp) (by decide) (by decide) (by norm_num))
  have hseq1 := DataStepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have hseq2 := DataStepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ hseq1 rfl h2
  have hseq3 := DataStepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ hseq2 rfl h3
  exact hseq3

theorem run_size_taken (input : ByteArray) (hfit : CalldataFits input)
    (hne : input.size ≠ 1000) :
    run sizePath (PatternedScan.stS input 27 []) = some (PatternedScan.stS input 247 []) := by
  have hj : run [opAt 22 .JUMPI]
      (PatternedScan.stS input 36 [246, sizeWord input]) =
      some (PatternedScan.stS input 246 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 22 36 _ (by norm_num) pc_g22)
      (PatternedScan.stepS_jumpi_taken input 36 246 246 _ []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _)
        (sizeWord_isTrue input hfit hne) generic_dest)
  have hd : run [entryDest] (PatternedScan.stS input 246 []) =
      some (PatternedScan.stS input 247 []) := by
    exact PatternedScan.blockOfS entryDest
      (PatternedScan.pcFactS input 147 246 [] (by norm_num)
        (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl))
      (PatternedScan.stepS_jumpdest input 246 [] (by simp) (by norm_num))
  have hje := DataStepper.runLocatedBlock_append [opAt 22 .JUMPI] [entryDest]
    _ _ _ hj rfl hd
  exact DataStepper.runLocatedBlock_append sizePrefix [opAt 22 .JUMPI, entryDest]
    _ _ _ (run_size_prefix input) rfl hje

theorem run_size_fall (input : ByteArray) (h : input.size = 1000) :
    run sizeFallPath (PatternedScan.stS input 27 []) = some (PatternedScan.stS input 37 []) := by
  have hj : run [opAt 22 .JUMPI]
      (PatternedScan.stS input 36 [246, sizeWord input]) =
      some (PatternedScan.stS input 37 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 22 36 _ (by norm_num) pc_g22)
      (PatternedScan.stepS_jumpi_fall input 36 246 _ [] (by simp) (by norm_num)
        (sizeWord_false input h))
  exact DataStepper.runLocatedBlock_append sizePrefix [opAt 22 .JUMPI] _ _ _
    (run_size_prefix input) rfl hj

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
