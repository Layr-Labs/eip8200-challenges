import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableScratch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableMemory
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScratch
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory StaggerTableMemory

def scratchMemory (memory : ByteArray) (low high : UInt256) : ByteArray :=
  writeWord (writeWord memory 60 high) 28 low

@[simp] theorem scratch_read_low (memory : ByteArray) (low high : UInt256) :
    MachineState.readWord (scratchMemory memory low high) 28 = low :=
  read_writeWord _ _ _

@[simp] theorem scratch_read_high (memory : ByteArray) (low high : UInt256) :
    MachineState.readWord (scratchMemory memory low high) 60 = high := by
  rw [scratchMemory, read_writeWord_disjoint _ _ _ _ (Or.inr (by decide)), read_writeWord]

def poolWord (memory : ByteArray) (i : Nat) : UInt256 :=
  Word.mask32 (MachineState.readWord memory (4 * i))

theorem poolWord_eq (memory : ByteArray) (low high : UInt256) (i : Nat) (hi : i < 16) :
    poolWord (scratchMemory memory low high) i =
      Word.mask32 (UInt256.shiftRight (if i < 8 then low else high)
        (UInt256.ofNat (32 * (7 - i % 8)))) := by
  by_cases hlow : i < 8
  · rw [if_pos hlow, Nat.mod_eq_of_lt hlow]
    have h := PairTableScratch.mask32_window (scratchMemory memory low high) 28 i (by decide) hlow
    rw [scratch_read_low] at h
    have ha : 28 + 4 * i - 28 = 4 * i := by omega
    simpa only [poolWord, ha] using h
  · rw [if_neg hlow]
    have hmod : i % 8 = i - 8 := by omega
    rw [hmod]
    have h := PairTableScratch.mask32_window (scratchMemory memory low high) 60 (i - 8) (by decide) (by omega)
    rw [scratch_read_high] at h
    have ha : 60 + 4 * (i - 8) - 28 = 4 * i := by omega
    simpa only [poolWord, ha] using h

private theorem chunk_eq_mask (value : UInt256) (j : Nat) (hj : j < 8) :
    PairedScheduleData.chunk value j =
      Word.mask32 (UInt256.shiftRight (PairedScheduleData.reversedWord value)
        (UInt256.ofNat (32 * (7 - j)))) := by
  by_cases h0 : j = 0
  · subst j
    simp only [PairedScheduleData.chunk, if_pos rfl, Nat.sub_zero]
    exact (DenseScheduleMemory.DensePacked.mask32_shr224 _).symm
  · by_cases h7 : j = 7
    · subst j
      simp only [PairedScheduleData.chunk, if_neg h0, if_pos rfl,
        Nat.sub_self, Nat.mul_zero]
      change Word.mask32 (PairedScheduleData.reversedWord value) = Word.mask32 (UInt256.shiftRight (PairedScheduleData.reversedWord value) (UInt256.ofNat 0))
      congr 1
      exact PairedScheduleData.shr_zero _ |>.symm
    · simp only [PairedScheduleData.chunk, if_neg h0, if_neg h7,
        DenseScheduleMemory.DensePacked.shr]

/-- All sixteen sources are clean 32-bit chunks before any table overwrite. -/
theorem poolWord_eq_extracted (memory : ByteArray) (p i : Nat) (hi : i < 16) :
    poolWord (scratchMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory p))
        (PairedScheduleData.reversedWord (MachineState.readWord memory (p + 32)))) i =
      PairedScheduleData.extractedWord memory p i := by
  rw [poolWord_eq _ _ _ _ hi, PairedScheduleData.extractedWord,
    chunk_eq_mask _ _ (Nat.mod_lt _ (by decide))]
  by_cases h : i < 8
  · rw [if_pos h, Nat.div_eq_of_lt h]
    simp only [Nat.mul_zero, Nat.add_zero]
  · rw [if_neg h]
    have hd : i / 8 = 1 := by omega
    rw [hd]

theorem erase_scratch (memory : ByteArray) (words : Nat → UInt256)
    (low high : UInt256) :
    storeDescending (scratchMemory memory low high) words 0 61 =
      storeDescending memory words 0 61 := by
  apply ByteArray.ext_getElem
  · rw [storeDescending_size _ _ _ _ (by omega),
      storeDescending_size _ _ _ _ (by omega)]
    simp only [scratchMemory, writeWord_size]
    omega
  · intro address hA hB
    rw [← Memory.getD0_eq_getElem _ _ hA, ← Memory.getD0_eq_getElem _ _ hB]
    by_cases hin : address < 1112
    · exact getD_storeDescending_inside _ _ _ _ _ _ (by omega) (by omega) (by simpa using hin)
    · rw [getD_table_outside _ _ _ (by omega), getD_table_outside _ _ _ (by omega)]
      simp only [scratchMemory, writeWord, MachineState.writeBytes_getElem?_getD,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      rw [if_neg (by omega), if_neg (by omega)]


/-! ## Words 1 and 2 without their mask

The loader stores schedule words 1 and 2 straight from the unaligned load.  While the first
memory word below the scratch block is a clean 32-bit word (the previous table's slot 0, or
untouched memory), those loads see zero bytes above the lower scratch word, so they carry
only the one or two schedule words that precede them. -/

def dirtyWord (memory : ByteArray) (p i : Nat) : UInt256 :=
  if i = 1 ∨ i = 2 then PairedScheduleData.extractedWordG memory p i
  else PairedScheduleData.extractedWord memory p i

def poolWordD (memory : ByteArray) (i : Nat) : UInt256 :=
  if i ≤ 2 then MachineState.readWord memory (4 * i) else poolWord memory i

private theorem extractedWordG_one_lt (memory : ByteArray) (p : Nat) :
    (PairedScheduleData.extractedWordG memory p 1).toNat < 2 ^ 64 := by
  have h : (PairedScheduleData.extractedWordG memory p 1).toNat =
      (UInt256.shiftRight (PairedScheduleData.reversedWord (MachineState.readWord memory p))
        (UInt256.ofNat 192)).toNat := by
    simp only [PairedScheduleData.extractedWordG, PairedScheduleData.chunkG,
      DenseScheduleMemory.DensePacked.shr, Nat.add_zero]
    norm_num
  rw [h, Word.shiftRight_toNat _ (by decide), Nat.shiftRight_eq_div_pow]
  have hx : (PairedScheduleData.reversedWord (MachineState.readWord memory p)).toNat < 2 ^ 256 :=
    (PairedScheduleData.reversedWord (MachineState.readWord memory p)).val.isLt
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add]
  exact hx

theorem dirtyWord_split (memory : ByteArray) (p k : Nat) :
    (dirtyWord memory p k).toNat =
        (PairedScheduleData.extractedWord memory p k).toNat +
          (dirtyWord memory p k).toNat / 2 ^ 32 * 2 ^ 32 ∧
      (dirtyWord memory p k).toNat / 2 ^ 32 < 2 ^ 64 ∧
      (k ≠ 2 → (dirtyWord memory p k).toNat / 2 ^ 32 < 2 ^ 32) ∧
      (¬ (k = 1 ∨ k = 2) → (dirtyWord memory p k).toNat / 2 ^ 32 = 0) := by
  have he := PairedScheduleData.extractedWord_bound memory p k
  by_cases hd : k = 1 ∨ k = 2
  · rw [dirtyWord, if_pos hd]
    obtain ⟨heq, hmod, hlt⟩ := PairedScheduleData.extractedWordG_eq_add memory p k
    have h1 : k ≠ 2 → (PairedScheduleData.extractedWordG memory p k).toNat < 2 ^ 64 := by
      intro h2
      have hk : k = 1 := by omega
      subst hk
      exact extractedWordG_one_lt memory p
    refine ⟨?_, ?_, fun h2 => ?_, fun h => absurd hd h⟩
    · simp only [Nat.reducePow] at *; omega
    · simp only [Nat.reducePow] at *; omega
    · have := h1 h2; simp only [Nat.reducePow] at *; omega
  · rw [dirtyWord, if_neg hd]
    simp only [Nat.reducePow] at *
    refine ⟨by omega, by omega, fun _ => by omega, fun _ => by omega⟩

/-- Bytes below the lower scratch word are those of the original memory. -/
private theorem scratch_prefix (memory : ByteArray) (low high : UInt256) (a n : Nat)
    (h : a + n ≤ 28) :
    Precompile.bytesToNatPadded (scratchMemory memory low high) a n =
      Precompile.bytesToNatPadded memory a n := by
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro i hi
  simp only [scratchMemory, writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (by omega), if_neg (by omega)]

/-- A clean first word leaves bytes `[0,28)` zero. -/
private theorem low_zero (memory : ByteArray)
    (hlow : (MachineState.readWord memory 0).toNat < 2 ^ 32) (a : Nat) (ha : a ≤ 28) :
    Precompile.bytesToNatPadded memory a (28 - a) = 0 := by
  rw [Bytes.readWord_toNat] at hlow
  have h32 := Bytes.bytesToNatPadded_add memory 0 28 4
  have h28 := Bytes.bytesToNatPadded_add memory 0 a (28 - a)
  rw [show a + (28 - a) = 28 by omega, Nat.zero_add] at h28
  rw [show (28 : Nat) + 4 = 32 by rfl] at h32
  have hpos : 0 < 256 ^ (28 - a) := Nat.pow_pos (by decide)
  have hb : Precompile.bytesToNatPadded memory 0 28 = 0 := by
    simp only [Nat.reducePow] at *
    omega
  rw [hb] at h28
  omega

private theorem scratch_window (memory : ByteArray) (low high : UInt256)
    (hlow : (MachineState.readWord memory 0).toNat < 2 ^ 32) (i : Nat) (hi : i ≤ 2) :
    (MachineState.readWord (scratchMemory memory low high) (4 * i)).toNat =
      low.toNat >>> (32 * (7 - i)) := by
  have hsplit := Bytes.bytesToNatPadded_add (scratchMemory memory low high) (4 * i) (28 - 4 * i)
    (4 + 4 * i)
  rw [show 28 - 4 * i + (4 + 4 * i) = 32 by omega, show 4 * i + (28 - 4 * i) = 28 by omega,
    scratch_prefix memory low high (4 * i) (28 - 4 * i) (by omega),
    low_zero memory hlow (4 * i) (by omega), Nat.zero_mul, Nat.zero_add] at hsplit
  rw [Bytes.readWord_toNat, hsplit,
    ← Bytes.readWord_shift_toNat (scratchMemory memory low high) 28 (4 + 4 * i) (by omega),
    scratch_read_low]
  congr 1
  omega

theorem poolWordD_eq_dirty (memory : ByteArray) (p i : Nat) (hi : i < 16)
    (hlow : (MachineState.readWord memory 0).toNat < 2 ^ 32) :
    poolWordD (scratchMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory p))
        (PairedScheduleData.reversedWord (MachineState.readWord memory (p + 32)))) i =
      dirtyWord memory p i := by
  by_cases hd : i ≤ 2
  · rw [poolWordD, if_pos hd]
    apply Word.word_ext
    rw [scratch_window memory _ _ hlow i hd]
    have hmod : i % 8 = i := by omega
    have hdiv : i / 8 = 0 := by omega
    by_cases h0 : i = 0
    · subst h0
      rw [dirtyWord, if_neg (by decide)]
      simp only [PairedScheduleData.extractedWord, PairedScheduleData.chunk, if_pos rfl,
        ite_true, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.zero_mod,
        DenseScheduleMemory.DensePacked.shr]
      change _ = (UInt256.shiftRight _ (UInt256.ofNat 224)).toNat
      rw [Word.shiftRight_toNat _ (by decide)]
    · have h12 : i = 1 ∨ i = 2 := by omega
      rw [dirtyWord, if_pos h12]
      simp only [PairedScheduleData.extractedWordG, PairedScheduleData.chunkG, hmod, hdiv,
        if_pos h12, Nat.mul_zero, Nat.add_zero, DenseScheduleMemory.DensePacked.shr]
      rw [Word.shiftRight_toNat _ (by omega)]
  · rw [poolWordD, if_neg hd, dirtyWord, if_neg (by omega)]
    exact poolWord_eq_extracted memory p i hi

#print axioms dirtyWord_split
#print axioms poolWordD_eq_dirty
#print axioms poolWord_eq_extracted
#print axioms erase_scratch
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScratch
