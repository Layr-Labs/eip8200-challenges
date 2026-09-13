import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableSparse
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlyMemory
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StaggerTableMemory StaggerTableLayout StaggerTableSparse

def keepPad (j : Nat) : Bool :=
  decide (slots[j]! = 0 ∨ slots[j]! = 14 ∨ slots[j]! = 15)

/-- Only the low pad-only length word carries dead high bits; the high word stays masked. -/
def lowDirty (n : UInt256) : UInt256 := UInt256.shiftLeft n (UInt256.ofNat 3)
def padWordsDirty (n : UInt256) (i : Nat) : UInt256 :=
  if i = 14 then lowDirty n else PadOnlySchedule.padWords n i

def resultMemory (memory : ByteArray) (n : UInt256) : ByteArray :=
  storeSelected (zeroMemory memory) (tableWords (padWordsDirty n)) keepPad 0 61

private theorem masked_bound (value : UInt256) :
    (UInt256.land (UInt256.ofNat 0xffffffff) value).toNat < 2 ^ 32 := by
  rw [Word.word_toNat_land]
  have hm : (UInt256.ofNat 0xffffffff).toNat = 0xffffffff := by decide
  rw [hm]
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by decide)

theorem padWords_bound (n : UInt256) (i : Nat) :
    (PadOnlySchedule.padWords n i).toNat < 2 ^ 32 := by
  unfold PadOnlySchedule.padWords
  split
  · decide
  · split
    · exact masked_bound _
    · split
      · exact masked_bound _
      · decide


theorem padWordsDirty_fourteen (n : UInt256) : padWordsDirty n 14 = lowDirty n := by
  simp [padWordsDirty]

theorem padWordsDirty_ne (n : UInt256) (i : Nat) (hi : i ≠ 14) :
    padWordsDirty n i = PadOnlySchedule.padWords n i := by
  simp [padWordsDirty, hi]

theorem lowLength_eq_padWords (n : UInt256) :
    PadOnlySchedule.lowLength n = PadOnlySchedule.padWords n 14 := by
  simp [PadOnlySchedule.padWords]

theorem lowDirty_shift (n : UInt256) (hn : n.toNat < 2 ^ 64) :
    (UInt256.shiftLeft n (UInt256.ofNat 3)).toNat = n.toNat * 2 ^ 3 := by
  have h := Word.shiftLeft_ofNat (value := n.toNat) (shift := 3) n.val.isLt (by decide)
    (by simp only [Nat.reducePow] at *; omega)
  rw [← Word.word_eq_ofNat_toNat n] at h
  rw [h, Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by simp only [Nat.reducePow] at *; omega)]

theorem lowDirty_toNat (n : UInt256) (hn : n.toNat < 2 ^ 64) :
    (lowDirty n).toNat = (PadOnlySchedule.lowLength n).toNat + n.toNat / 2 ^ 29 * 2 ^ 32 := by
  have hs := lowDirty_shift n hn
  unfold PadOnlySchedule.lowLength lowDirty
  rw [Word.word_toNat_land, hs]
  have hm : (UInt256.ofNat 0xffffffff).toNat = 2 ^ 32 - 1 := by decide
  rw [hm, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.reducePow]
  omega

theorem lowDirty_junk_lt (n : UInt256) (hn : n.toNat < 2 ^ 64) : n.toNat / 2 ^ 29 < 2 ^ 35 := by
  simp only [Nat.reducePow] at *
  omega

theorem padWordsDirty_bound (n : UInt256) (hn : n.toNat < 2 ^ 64) (i : Nat) :
    (padWordsDirty n i).toNat < 2 ^ 112 := by
  unfold padWordsDirty
  split
  · unfold lowDirty
    rw [lowDirty_shift n hn]
    simp only [Nat.reducePow] at *
    omega
  · exact Nat.lt_trans (padWords_bound n i) (by decide)

theorem resultMemory_eq_table (memory : ByteArray) (n : UInt256) (hn : n.toNat < 2 ^ 64) :
    resultMemory memory n = StaggerTableLayout.resultMemory memory (padWordsDirty n) := by
  unfold resultMemory
  refine (selected_eq_full memory (tableWords (padWordsDirty n)) keepPad 0 61
    (by decide) ?_ ?_).trans (erase_zeroMemory _ _)
  · intro j hj hj'
    exact padWordsDirty_bound n hn slots[j]!
  · intro j hj hj' hk
    have h : ¬ (slots[j]! = 0 ∨ slots[j]! = 14 ∨ slots[j]! = 15) :=
      of_decide_eq_false hk
    simp only [tableWords, padWordsDirty, PadOnlySchedule.padWords,
      if_neg (show slots[j]! ≠ 0 by omega), if_neg (show slots[j]! ≠ 14 by omega),
      if_neg (show slots[j]! ≠ 15 by omega)]

theorem read_resultMemory_outside (memory : ByteArray) (n : UInt256)
    (address : Nat) (ha : 1112 ≤ address) :
    MachineState.readWord (resultMemory memory n) address = MachineState.readWord memory address := by
  unfold MachineState.readWord
  congr 2
  apply Memory.readPadded_congr
  intro i hi
  unfold resultMemory
  rw [getD_storeSelected_outside _ _ _ _ _ _ (fun k hk hk' => by omega),
    zeroMemory_getD, if_neg (by omega)]


/-! ## M3b: the pad-only block stores in program order

The low block stores the unmasked low bit-length word `n <<< 3` at 162, 666, 144 and `0x80` at
522, 54, 36;
when `n >>> 29 ≠ 0` the high block then stores the masked high word at 1008, 990, 648, 612, 270.
Only adjacent slots (18 bytes apart) overlap, and every overlapping pair is still written
higher-address first, so the result is the descending table store. -/

theorem padWriteWord_comm (memory : ByteArray) (a b : Nat) (va vb : UInt256)
    (hab : a + 32 ≤ b ∨ b + 32 ≤ a) :
    PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord memory a va) b vb =
      PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord memory b vb) a va := by
  apply ByteArray.ext_getElem
  · simp only [PairedScheduleMemory.writeWord_size]
    omega
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj]
    simp only [PairedScheduleMemory.writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases ha : a ≤ i ∧ i < a + 32
    · have hb : ¬ (b ≤ i ∧ i < b + 32) := by omega
      simp only [if_pos ha, if_neg hb]
    · by_cases hb : b ≤ i ∧ i < b + 32
      · simp only [if_pos hb, if_neg ha]
      · simp only [if_neg ha, if_neg hb]

def keepLow (j : Nat) : Bool :=
  decide (slots[j]! = 0 ∨ slots[j]! = 14)

/-- Memory after the low block (program order). -/
def lowChain (memory : ByteArray) (n : UInt256) : ByteArray :=
  PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord
    (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord
      (zeroMemory memory) 162 (lowDirty n)) 666 (lowDirty n))
      144 (lowDirty n)) 522 (UInt256.ofNat 128)) 54 (UInt256.ofNat 128))
    36 (UInt256.ofNat 128)

/-- The high block stores the masked high bit-length word in program order. -/
def highStores (memory : ByteArray) (n : UInt256) : ByteArray :=
  PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord
    (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord memory
      1008 (PadOnlySchedule.highLength n)) 990 (PadOnlySchedule.highLength n)) 648 (PadOnlySchedule.highLength n)) 612 (PadOnlySchedule.highLength n)) 270 (PadOnlySchedule.highLength n)

theorem highChain_eq (memory : ByteArray) (n : UInt256) :
    highStores (lowChain memory n) n = resultMemory memory n := by
  unfold highStores lowChain
  rw [padWriteWord_comm _ 162 666 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 522 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 36 1008 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 36 990 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 36 648 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 36 612 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 36 270 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 522 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 54 1008 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 54 990 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 54 648 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 54 612 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 54 270 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 1008 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 990 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 648 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 612 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 270 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 1008 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 990 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 648 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 612 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 270 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 522 1008 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 522 990 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 522 648 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 522 612 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 666 1008 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 666 990 _ _ (Or.inl (by decide))]
  simp [resultMemory, storeSelected, keepPad, tableWords, slots, padWordsDirty, PadOnlySchedule.padWords,
    PadOnlySchedule.padWords]

theorem lowChain_selected (memory : ByteArray) (n : UInt256) :
    lowChain memory n = storeSelected (zeroMemory memory) (tableWords (padWordsDirty n)) keepLow 0 61 := by
  unfold lowChain
  rw [padWriteWord_comm _ 162 666 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 522 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 522 _ _ (Or.inl (by decide))]
  simp [storeSelected, keepLow, tableWords, slots, padWordsDirty, PadOnlySchedule.padWords, PadOnlySchedule.padWords]

theorem lowChain_eq (memory : ByteArray) (n : UInt256)
    (hz : UInt256.shiftRight n (UInt256.ofNat 29) = UInt256.ofNat 0) :
    lowChain memory n = resultMemory memory n := by
  have hnat := congrArg UInt256.toNat hz
  rw [Word.shiftRight_toNat _ (by decide), Nat.shiftRight_eq_div_pow] at hnat
  have hn : n.toNat < 2 ^ 64 := by
    change n.toNat / 2 ^ 29 = 0 at hnat
    simp only [Nat.reducePow] at hnat ⊢
    omega
  have hhigh : PadOnlySchedule.highLength n = UInt256.ofNat 0 := by
    rw [PadOnlySchedule.highLength, hz]
    decide
  rw [lowChain_selected]
  unfold resultMemory
  rw [selected_eq_full memory (tableWords (padWordsDirty n)) keepLow 0 61 (by decide)
      (fun j _ _ => padWordsDirty_bound n hn slots[j]!) ?_,
    selected_eq_full memory (tableWords (padWordsDirty n)) keepPad 0 61 (by decide)
      (fun j _ _ => padWordsDirty_bound n hn slots[j]!) ?_]
  · intro j hj hj' hk
    have h : ¬ (slots[j]! = 0 ∨ slots[j]! = 14 ∨ slots[j]! = 15) := by simpa [keepPad] using hk
    simp only [tableWords, padWordsDirty, PadOnlySchedule.padWords, PadOnlySchedule.padWords,
      if_neg (show slots[j]! ≠ 0 by omega), if_neg (show slots[j]! ≠ 14 by omega),
      if_neg (show slots[j]! ≠ 15 by omega)]
  · intro j hj hj' hk
    have h : ¬ (slots[j]! = 0 ∨ slots[j]! = 14) := by simpa [keepLow] using hk
    by_cases h15 : slots[j]! = 15
    · simp [tableWords, padWordsDirty, PadOnlySchedule.padWords, h15, hhigh]
    · simp only [tableWords, padWordsDirty, PadOnlySchedule.padWords, PadOnlySchedule.padWords,
        if_neg (show slots[j]! ≠ 0 by omega), if_neg (show slots[j]! ≠ 14 by omega),
        if_neg h15]

theorem readPadded_end (input : ByteArray) :
    MachineState.readPadded input input.size 1112 = StaggerTableSparse.zeroBytes := by
  simp [MachineState.readPadded, StaggerTableSparse.zeroBytes]

#print axioms highChain_eq
#print axioms lowChain_eq
#print axioms padWords_bound
#print axioms resultMemory_eq_table
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
