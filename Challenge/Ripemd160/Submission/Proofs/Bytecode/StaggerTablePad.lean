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

theorem readPadded_end (input : ByteArray) :
    MachineState.readPadded input input.size 632 = StaggerTableSparse.zeroBytes := by
  simp [MachineState.readPadded, StaggerTableSparse.zeroBytes]

#print axioms padWords_bound
#print axioms resultMemory_eq_table
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
