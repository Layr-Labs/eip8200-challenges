import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Zero
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# Word-0 schedule reads of the fast pad-only block

Word 0 of a pad-only block is `0x80`.  A table read at `18 * j` packs slot `j` in the low
lane and slot `j - 1` at bit 144, so the five reads below, whose slots hold only word 0 and
zero words, are constants.  The specialised compressor folds them into its round keys.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

structure PadWord0 (m : ByteArray) : Prop where
  r36 : MachineState.readWord m 36 = UInt256.ofNat 128
  r54 : MachineState.readWord m 54 = UInt256.ofNat 2854495385411919762116571938898990272765493376
  r72 : MachineState.readWord m 72 = UInt256.ofNat 2854495385411919762116571938898990272765493248
  r522 : MachineState.readWord m 522 = UInt256.ofNat 128
  r540 : MachineState.readWord m 540 = UInt256.ofNat 2854495385411919762116571938898990272765493248

theorem table_word_head (n : UInt256) : StaggerTablePad.padWordsDirty n 0 = UInt256.ofNat 128 := by
  rw [StaggerTablePad.padWordsDirty_ne _ _ (by decide) (by decide)]
  simp [PadOnlySchedule.padWords]

private theorem read_slot (m : ByteArray) (n : UInt256) (hn : n.toNat < 2 ^ 29) (j : Nat)
    (hj1 : 2 ≤ j) (hj : j < 61) (a b : Nat) (hta : (UInt256.ofNat a).toNat = a)
    (htb : (UInt256.ofNat b).toNat = b) (ha32 : a < 2 ^ 32) (hb32 : b < 2 ^ 32)
    (ha : StaggerTablePad.padWordsDirty n StaggerTableLayout.slots[j]! = UInt256.ofNat a)
    (hb : StaggerTablePad.padWordsDirty n StaggerTableLayout.slots[j - 1]! = UInt256.ofNat b) :
    (MachineState.readWord (StaggerTablePad.padRealResult m n) (18 * j)).toNat = a + b * 2 ^ 144 := by
  have hn64 : n.toNat < 2 ^ 64 := Nat.lt_trans hn (by decide)
  rw [read_from28 m n _ (by omega), StaggerTablePad.resultMemory_eq_table m n hn64]
  unfold StaggerTableLayout.resultMemory
  rw [StaggerTableMemory.read_pair m (StaggerTableLayout.tableWords (StaggerTablePad.padWordsDirty n))
    0 61 j (by omega) (by omega)
    (by simp only [StaggerTableLayout.tableWords, ha, hta]; exact ha32)
    (by simp only [StaggerTableLayout.tableWords, hb, htb]; exact hb32)]
  simp only [StaggerTableLayout.tableWords, ha, hb, hta, htb]

private theorem toNat128 : (UInt256.ofNat 128).toNat = 128 := by decide
private theorem toNat0 : (UInt256.ofNat 0).toNat = 0 := by decide

private theorem read_value (m : ByteArray) (n : UInt256) (A : Nat) (c : Nat) (hc : c < 2 ^ 256)
    (h : (MachineState.readWord (StaggerTablePad.padRealResult m n) A).toNat = c) :
    MachineState.readWord (StaggerTablePad.padRealResult m n) A = UInt256.ofNat c := by
  apply Word.word_ext
  rw [h, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hc]

theorem padWord0 (m : ByteArray) (n : UInt256) (hn : n.toNat < 2 ^ 29) :
    PadWord0 (StaggerTablePad.padRealResult m n) := by
  have z (k : Nat) (h0 : k ≠ 0) (h14 : k ≠ 14) := table_word_zero n hn k h0 h14
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact read_value m n 36 128 (by decide)
      (read_slot m n hn 2 (by decide) (by decide) 128 0 toNat128 toNat0 (by decide) (by decide)
        (table_word_head n) (z _ (by decide) (by decide)))
  · exact read_value m n 54 _ (by decide)
      (read_slot m n hn 3 (by decide) (by decide) 128 128 toNat128 toNat128 (by decide) (by decide)
        (table_word_head n) (table_word_head n))
  · exact read_value m n 72 _ (by decide)
      (read_slot m n hn 4 (by decide) (by decide) 0 128 toNat0 toNat128 (by decide) (by decide)
        (z _ (by decide) (by decide)) (table_word_head n))
  · exact read_value m n 522 128 (by decide)
      (read_slot m n hn 29 (by decide) (by decide) 128 0 toNat128 toNat0 (by decide) (by decide)
        (table_word_head n) (z _ (by decide) (by decide)))
  · exact read_value m n 540 _ (by decide)
      (read_slot m n hn 30 (by decide) (by decide) 0 128 toNat0 toNat128 (by decide) (by decide)
        (z _ (by decide) (by decide)) (table_word_head n))

#print axioms padWord0
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy
