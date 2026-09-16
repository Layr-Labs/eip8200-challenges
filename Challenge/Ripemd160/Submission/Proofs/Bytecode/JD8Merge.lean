import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreMerge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreGap

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# The 48-store writer bridge for DIRTY source words

`PairStoreMerge.three_store_merge` requires `hw : w.toNat < 2 ^ 32`.  The bytes that force it
are the four-byte gap `[a-4, a)`: the three-store form writes bits 112..143 of the middle value
there, the merged form writes nothing, so they agree only when those bits are zero.  When the
source word carries junk into bits 32..143 the merge is FALSE as stated.

The lemma below is stated ABSTRACTLY in the stored value `P`, with no MUL, no OR and no bound
on the source: whatever the pool leaves on the stack, the merge holds as long as `P`'s low 144
bits are the surviving slot's and `P`'s high bits are what the elided slot is modelled to hold.
Taking the modelled middle value to BE `hi144 P` makes all three side conditions free:
`hhi` is definitional, `hm` is `hi144_lt`, and `hlo` is `rfl`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Merge
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory PairStoreMerge

/-- The high half of a stored dual lane: what the ELIDED slot ends up holding. -/
def hi144 (x : UInt256) : UInt256 := UInt256.ofNat (x.toNat / 2 ^ 144)

theorem hi144_toNat (x : UInt256) : (hi144 x).toNat = x.toNat / 2 ^ 144 := by
  rw [hi144, Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) x.val.isLt

theorem hi144_lt (x : UInt256) : (hi144 x).toNat < 2 ^ 112 := by
  rw [hi144_toNat]
  exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact x.val.isLt)

/-- Byte `k < 14` of a word is byte `k+18` of its own high half. -/
theorem byte_of_high (P m : UInt256) (h : P.toNat / 2 ^ 144 = m.toNat) (k : Nat) (hk : k < 14) :
    (Data.Bytes.natToBytesPadded P.toNat 32)[k]?.getD 0
      = (Data.Bytes.natToBytesPadded m.toNat 32)[k + 18]?.getD 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega),
    YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega)]
  have hexp : (256 : Nat) ^ (32 - 1 - k) = 2 ^ 144 * 256 ^ (13 - k) := by
    interval_cases k <;> norm_num
  have hidx : 32 - 1 - (k + 18) = 13 - k := by omega
  rw [hexp, ← Nat.div_div_eq_div_mul, h, hidx]

/-- **The bridge, stated once.**  The middle store of a table-adjacent triple may be dropped
provided the surviving store's value `P` carries the middle slot's content in its high half.
No bound on the source word at all; the only bound is that the modelled middle value fits the
fourteen bytes that survive, `m < 2 ^ 112`, which is what makes the exposed four-byte gap zero
on both sides. -/
theorem three_store_merge_abs (memory : ByteArray) (a : Nat) (P m w v : UInt256)
    (ha : 36 ≤ a) (hm : m.toNat < 2 ^ 112)
    (hlo : P.toNat % 2 ^ 144 = w.toNat % 2 ^ 144)
    (hhi : P.toNat / 2 ^ 144 = m.toNat)
    (hgap : ∀ i, a - 4 ≤ i → i < a → memory[i]?.getD 0 = 0) :
    writeWord (writeWord (writeWord memory a w) (a - 18) m) (a - 36) v =
      writeWord (writeWord memory a P) (a - 36) v := by
  apply ByteArray.ext_getElem
  · simp only [writeWord_size]
    omega
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases hlow : a - 36 ≤ i ∧ i < a - 36 + 32
    · simp only [if_pos hlow]
    · simp only [if_neg hlow]
      by_cases hmid : a - 18 ≤ i ∧ i < a - 18 + 32
      · rw [if_pos hmid]
        by_cases hin : a ≤ i ∧ i < a + 32
        · rw [if_pos hin, byte_of_high P m hhi (i - a) (by omega)]
          congr 2
          omega
        · rw [if_neg hin, PairStoreGap.encoded_prefix_zero m hm _ (by omega)]
          exact (hgap i (by omega) (by omega)).symm
      · rw [if_neg hmid]
        by_cases hin : a ≤ i ∧ i < a + 32
        · rw [if_pos hin, if_pos hin]
          exact (StaggerTableLayout.byte_of_mod P w hlo (i - a) (by omega) (by omega)).symm
        · rw [if_neg hin, if_neg hin]

/-- The instance every merge site uses: the modelled middle value is the surviving store's own
high half, so the merge costs NO hypothesis about the word. -/
theorem three_store_merge_hi (memory : ByteArray) (a : Nat) (P v : UInt256) (ha : 36 ≤ a)
    (hgap : ∀ i, a - 4 ≤ i → i < a → memory[i]?.getD 0 = 0) :
    writeWord (writeWord (writeWord memory a P) (a - 18) (hi144 P)) (a - 36) v =
      writeWord (writeWord memory a P) (a - 36) v :=
  three_store_merge_abs memory a P (hi144 P) P v ha (hi144_lt P) rfl (hi144_toNat P).symm hgap

#print axioms three_store_merge_abs
#print axioms three_store_merge_hi
end Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Merge
