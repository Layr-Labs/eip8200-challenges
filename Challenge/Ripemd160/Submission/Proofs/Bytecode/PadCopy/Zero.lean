import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PoolPadInvariant
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# Zero schedule words of the fast pad-only block

The fast pad-only block (calldata length a multiple of 64 below 256) leaves the
descending schedule table holding only message words 0, 14 and 15.  Word 15 is
`n >>> 29`, which is zero for such lengths, and every other word is zero.  A table
read at `18 * j` sees exactly slots `j` and `j - 1`, so each read below whose two
slots avoid words 0 and 14 returns zero.  The specialised pad-only compressor omits
those reads.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

/-- Table slots whose reads the specialised compressor omits (address `18 * j`). -/
def zeroSlots : List Nat :=
  [5, 6, 7, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 31, 32, 33,
   34, 35, 36, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58,
   59, 60]

def PadZero (m : ByteArray) : Prop :=
  ∀ j ∈ zeroSlots, MachineState.readWord m (18 * j) = UInt256.ofNat 0

theorem read_from28 (m : ByteArray) (n : UInt256) (A : Nat) (hA : 28 ≤ A) :
    MachineState.readWord (StaggerTablePad.padRealResult m n) A =
      MachineState.readWord (StaggerTablePad.resultMemory m n) A := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  exact StaggerTableMemory.bytesToNatPadded_congrOffset _ _ _ _ _
    (fun i _ => HoistedInherited.PoolPadInvariant.padRealResult_from28 m n (A + i) (by omega))

theorem table_word_zero (n : UInt256) (hn : n.toNat < 2 ^ 29) (k : Nat)
    (h0 : k ≠ 0) (h14 : k ≠ 14) :
    StaggerTablePad.padWordsDirty n k = UInt256.ofNat 0 := by
  by_cases h15 : k = 15
  · subst h15
    rw [StaggerTablePad.padWordsDirty_fifteen]
    apply Word.word_ext
    unfold StaggerTablePad.highDirty
    rw [Word.shiftRight_toNat _ (by decide), Nat.shiftRight_eq_div_pow, Word.word_toNat_ofNat]
    have : n.toNat / 2 ^ 29 = 0 := Nat.div_eq_of_lt hn
    rw [this]
    rfl
  · rw [StaggerTablePad.padWordsDirty_ne _ _ h14 h15]
    simp [PadOnlySchedule.padWords, h0, h14, h15]

theorem read_slot_zero (m : ByteArray) (n : UInt256) (hn : n.toNat < 2 ^ 29) (j : Nat)
    (hj1 : 2 ≤ j) (hj : j < 61)
    (ha : StaggerTablePad.padWordsDirty n StaggerTableLayout.slots[j]! = UInt256.ofNat 0)
    (hb : StaggerTablePad.padWordsDirty n StaggerTableLayout.slots[j - 1]! = UInt256.ofNat 0) :
    MachineState.readWord (StaggerTablePad.padRealResult m n) (18 * j) = UInt256.ofNat 0 := by
  have hn64 : n.toNat < 2 ^ 64 := Nat.lt_trans hn (by decide)
  rw [read_from28 m n _ (by omega), StaggerTablePad.resultMemory_eq_table m n hn64]
  apply Word.word_ext
  unfold StaggerTableLayout.resultMemory
  have hz : (UInt256.ofNat 0).toNat = 0 := by decide
  rw [StaggerTableMemory.read_pair m (StaggerTableLayout.tableWords (StaggerTablePad.padWordsDirty n))
    0 61 j (by omega) (by omega)
    (by simp only [StaggerTableLayout.tableWords, ha, hz]; decide)
    (by simp only [StaggerTableLayout.tableWords, hb, hz]; decide)]
  simp only [StaggerTableLayout.tableWords, ha, hb, hz, Nat.zero_mul, Nat.add_zero]

private theorem slots_ok : ∀ j ∈ zeroSlots, 2 ≤ j ∧ j < 61 ∧
    StaggerTableLayout.slots[j]! ≠ 0 ∧ StaggerTableLayout.slots[j]! ≠ 14 ∧
    StaggerTableLayout.slots[j - 1]! ≠ 0 ∧ StaggerTableLayout.slots[j - 1]! ≠ 14 := by
  decide

theorem padZero (m : ByteArray) (n : UInt256) (hn : n.toNat < 2 ^ 29) :
    PadZero (StaggerTablePad.padRealResult m n) := by
  intro j hj
  obtain ⟨h1, h61, ha0, ha14, hb0, hb14⟩ := slots_ok j hj
  exact read_slot_zero m n hn j h1 h61 (table_word_zero n hn _ ha0 ha14)
    (table_word_zero n hn _ hb0 hb14)

#print axioms padZero
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy
