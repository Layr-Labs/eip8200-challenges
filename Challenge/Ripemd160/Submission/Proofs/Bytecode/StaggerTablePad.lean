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

def resultMemory (memory : ByteArray) (n : UInt256) : ByteArray :=
  storeSelected (zeroMemory memory) (tableWords (PadOnlySchedule.padWords n)) keepPad 0 61

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

theorem resultMemory_eq_table (memory : ByteArray) (n : UInt256) :
    resultMemory memory n = StaggerTableLayout.resultMemory memory (PadOnlySchedule.padWords n) := by
  unfold resultMemory
  refine (selected_eq_full memory (tableWords (PadOnlySchedule.padWords n)) keepPad 0 61
    (by decide) ?_ ?_).trans (erase_zeroMemory _ _)
  · intro j hj hj'
    exact padWords_bound n slots[j]!
  · intro j hj hj' hk
    have h : ¬ (slots[j]! = 0 ∨ slots[j]! = 14 ∨ slots[j]! = 15) :=
      of_decide_eq_false hk
    simp only [tableWords, PadOnlySchedule.padWords,
      if_neg (show slots[j]! ≠ 0 by omega), if_neg (show slots[j]! ≠ 14 by omega),
      if_neg (show slots[j]! ≠ 15 by omega)]

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
      (zeroMemory memory) 162 (PadOnlySchedule.lowLength n)) 666 (PadOnlySchedule.lowLength n))
      144 (PadOnlySchedule.lowLength n)) 522 (UInt256.ofNat 128)) 54 (UInt256.ofNat 128))
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
  simp [resultMemory, storeSelected, keepPad, tableWords, slots, PadOnlySchedule.padWords,
    PadOnlySchedule.padWords]

theorem lowChain_selected (memory : ByteArray) (n : UInt256) :
    lowChain memory n = storeSelected (zeroMemory memory) (tableWords (PadOnlySchedule.padWords n)) keepLow 0 61 := by
  unfold lowChain
  rw [padWriteWord_comm _ 162 666 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 522 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 522 _ _ (Or.inl (by decide))]
  simp [storeSelected, keepLow, tableWords, slots, PadOnlySchedule.padWords, PadOnlySchedule.padWords]

theorem lowChain_eq (memory : ByteArray) (n : UInt256) (hz : PadOnlySchedule.highLength n = UInt256.ofNat 0) :
    lowChain memory n = resultMemory memory n := by
  rw [lowChain_selected]
  unfold resultMemory
  rw [selected_eq_full memory (tableWords (PadOnlySchedule.padWords n)) keepLow 0 61 (by decide)
      (fun j _ _ => padWords_bound n slots[j]!) ?_,
    selected_eq_full memory (tableWords (PadOnlySchedule.padWords n)) keepPad 0 61 (by decide)
      (fun j _ _ => padWords_bound n slots[j]!) ?_]
  · intro j hj hj' hk
    have h : ¬ (slots[j]! = 0 ∨ slots[j]! = 14 ∨ slots[j]! = 15) := by simpa [keepPad] using hk
    simp only [tableWords, PadOnlySchedule.padWords, PadOnlySchedule.padWords,
      if_neg (show slots[j]! ≠ 0 by omega), if_neg (show slots[j]! ≠ 14 by omega),
      if_neg (show slots[j]! ≠ 15 by omega)]
  · intro j hj hj' hk
    have h : ¬ (slots[j]! = 0 ∨ slots[j]! = 14) := by simpa [keepLow] using hk
    by_cases h15 : slots[j]! = 15
    · simp [tableWords, PadOnlySchedule.padWords, h15, hz]
    · simp only [tableWords, PadOnlySchedule.padWords, PadOnlySchedule.padWords,
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
