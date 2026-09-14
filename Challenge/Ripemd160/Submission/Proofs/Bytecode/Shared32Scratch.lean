import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreGap

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Scratch
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory

def highWord : UInt256 := UInt256.ofNat (2 ^ 231 + 2 ^ 40)

def sparseMemory (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes memory (ByteArray.mk #[128]) 63)
    (ByteArray.mk #[1]) 86

theorem highWord_bytes : Data.Bytes.natToBytesPadded highWord.toNat 32 =
    ByteArray.mk #[0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by
  apply ByteArray.ext_getElem
  · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; rfl
  · intro i hA hB
    have hi : i < 32 := hB
    rw [← Memory.getD0_eq_getElem _ _ hA, ← Memory.getD0_eq_getElem _ _ hB,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
    interval_cases i <;> norm_num [highWord, Word.word_toNat_ofNat] <;> rfl

/-- The sparse stores equal the upper endian scratch word on fresh scratch bytes. -/
theorem sparse_eq_writeWord (memory : ByteArray) (hsize : 92 ≤ memory.size)
    (hzero : ∀ a, 60 ≤ a → a < 92 → memory[a]?.getD 0 = 0) :
    sparseMemory memory = writeWord memory 60 highWord := by
  apply ByteArray.ext_getElem
  · simp only [sparseMemory, MachineState.writeBytes_size, writeWord, highWord_bytes]
    have h1 : (ByteArray.mk #[1]) ≠ ByteArray.empty := by decide
    have h128 : (ByteArray.mk #[128]) ≠ ByteArray.empty := by decide
    try simp only [if_neg h1, if_neg h128]
    have h32 : (Data.Bytes.natToBytesPadded highWord.toNat 32) ≠ ByteArray.empty := by
      intro h
      have := congrArg ByteArray.size h
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] at this
      contradiction
    rw [highWord_bytes] at h32
    try simp only [if_neg h32]
    change max (max memory.size 64) 87 = max memory.size 92
    omega
  · intro a hA hB
    rw [← Memory.getD0_eq_getElem _ _ hA, ← Memory.getD0_eq_getElem _ _ hB]
    simp only [sparseMemory, writeWord, highWord_bytes,
      MachineState.writeBytes_getElem?_getD]
    change (if 86 ≤ a ∧ a < 87 then (ByteArray.mk #[1])[a - 86]?.getD 0
      else if 63 ≤ a ∧ a < 64 then (ByteArray.mk #[128])[a - 63]?.getD 0
      else memory[a]?.getD 0) =
      if 60 ≤ a ∧ a < 92 then _ else memory[a]?.getD 0
    by_cases h60 : 60 ≤ a
    · by_cases h92 : a < 92
      · have hz := hzero a h60 h92
        interval_cases a <;> simp_all <;> rfl
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

def copiedMemory (input : ByteArray) : ByteArray :=
  MachineState.writeBytes ByteArray.empty input 1120

theorem copiedMemory_size (input : ByteArray) (hn : 0 < input.size) :
    (copiedMemory input).size = 1120 + input.size := by
  have hne : input ≠ ByteArray.empty := by intro h; subst input; exact Nat.not_lt_zero _ hn
  simp [copiedMemory, MachineState.writeBytes_size, hne]

theorem copiedMemory_zero (input : ByteArray) (a : Nat) (ha : a < 1120) :
    (copiedMemory input)[a]?.getD 0 = 0 := by
  simp [copiedMemory, MachineState.writeBytes_getElem?_getD, show ¬1120 ≤ a by omega]

theorem copiedMemory_sparse (input : ByteArray) (hn : 0 < input.size) :
    sparseMemory (copiedMemory input) = writeWord (copiedMemory input) 60 highWord :=
  sparse_eq_writeWord _ (by rw [copiedMemory_size input hn]; omega)
    (fun a _ h => copiedMemory_zero input a (by omega))

theorem copiedMemory_gapClear (input : ByteArray) :
    PairStoreGap.GapClear (copiedMemory input) := by
  intro j hj k hk0 hk1
  have hb := PairStoreGap.lowerPairSlots_bounds j hj
  exact copiedMemory_zero input _ (by omega)

theorem scratch_read_prefix (memory : ByteArray) (low high high' : UInt256)
    (a : Nat) (ha : a + 32 ≤ 60) :
    MachineState.readWord (StaggerScratch.scratchMemory memory low high) a =
      MachineState.readWord (StaggerScratch.scratchMemory memory low high') a := by
  apply Word.word_ext
  simp only [Bytes.readWord_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro j hj
  simp only [StaggerScratch.scratchMemory, writeWord,
    MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  by_cases hw : 28 ≤ a + j ∧ a + j < 28 + 32
  · rw [if_pos hw, if_pos hw]
  · rw [if_neg hw, if_neg hw, if_neg (by omega), if_neg (by omega)]

/-- Replacing only the upper scratch word preserves all eight lower schedule words. -/
theorem pool_lower (memory : ByteArray) (p i : Nat) (high : UInt256)
    (hi : i < 8) (hlow : (MachineState.readWord memory 0).toNat < 2 ^ 32) :
    StaggerScratch.poolWordD
      (StaggerScratch.scratchMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory p)) high) i =
      StaggerScratch.dirtyWord memory p i := by
  rw [← StaggerScratch.poolWordD_eq_dirty memory p i (by omega) hlow]
  by_cases hd : i ≤ 2
  · simp only [StaggerScratch.poolWordD, if_pos hd]
    exact scratch_read_prefix _ _ _ _ _ (by omega)
  · simp only [StaggerScratch.poolWordD, if_neg hd]
    rw [StaggerScratch.poolWord_eq _ _ _ _ (by omega),
      StaggerScratch.poolWord_eq _ _ _ _ (by omega), if_pos hi, if_pos hi]

theorem pool_upper (memory : ByteArray) (low : UInt256) (i : Nat)
    (hi0 : 8 ≤ i) (hi1 : i < 16) :
    StaggerScratch.poolWordD (StaggerScratch.scratchMemory memory low highWord) i =
      UInt256.ofNat (if i = 8 then 128 else if i = 14 then 256 else 0) := by
  rw [StaggerScratch.poolWordD, if_neg (by omega),
    StaggerScratch.poolWord_eq _ _ _ _ hi1, if_neg (by omega)]
  interval_cases i <;> rfl

#print axioms sparse_eq_writeWord
#print axioms copiedMemory_sparse
#print axioms copiedMemory_gapClear
#print axioms pool_lower
#print axioms pool_upper
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Scratch
