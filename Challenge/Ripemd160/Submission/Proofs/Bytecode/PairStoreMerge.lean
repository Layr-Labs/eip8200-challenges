import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreMerge
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory

def packed (w : UInt256) : UInt256 := UInt256.mul w (UInt256.ofNat (2 ^ 144 + 1))

theorem pack_nat_bound (n : Nat) (hn : n < 2 ^ 32) :
    n * (2 ^ 144 + 1) < 2 ^ 176 := by
  have hnle : n ≤ 2 ^ 32 - 1 := by omega
  calc
    n * (2 ^ 144 + 1) ≤ (2 ^ 32 - 1) * (2 ^ 144 + 1) :=
      Nat.mul_le_mul_right _ hnle
    _ < 2 ^ 176 := by norm_num

theorem mul_toNat (a b : UInt256) :
    (UInt256.mul a b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

theorem packed_toNat (w : UInt256) (hw : w.toNat < 2 ^ 32) :
    (packed w).toNat = w.toNat * (2 ^ 144 + 1) := by
  have hb : w.toNat * (2 ^ 144 + 1) < 2 ^ 256 :=
    (pack_nat_bound _ hw).trans (by norm_num)
  unfold packed
  rw [mul_toNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : (2 : Nat) ^ 144 + 1 < 2 ^ 256),
    Nat.mod_eq_of_lt hb]

theorem byte_pack_nat (n i : Nat) (hn : n < 2 ^ 32) (hi : i < 32) :
    n * (2 ^ 144 + 1) / 256 ^ (32 - 1 - i) % 256 =
      if 10 ≤ i ∧ i < 14 then n / 256 ^ (32 - 1 - (i + 18)) % 256
      else n / 256 ^ (32 - 1 - i) % 256 := by
  by_cases h10 : i < 10
  · have hp : (2 : Nat) ^ 176 ≤ 256 ^ (32 - 1 - i) := by
      calc
        (2 : Nat) ^ 176 = 256 ^ 22 := by norm_num
        _ ≤ 256 ^ (32 - 1 - i) := Nat.pow_le_pow_right (by decide) (by omega)
    have hp0 : (2 : Nat) ^ 32 ≤ 256 ^ (32 - 1 - i) :=
      (by norm_num : (2 : Nat) ^ 32 ≤ 2 ^ 176).trans hp
    rw [if_neg (by omega), Nat.div_eq_of_lt ((pack_nat_bound n hn).trans_le hp),
      Nat.div_eq_of_lt (hn.trans_le hp0)]
  · by_cases h14 : i < 14
    · have hdiv : n * (2 ^ 144 + 1) / 2 ^ 144 = n := by
        have hnR : n < 2 ^ 144 := hn.trans (by norm_num)
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm n (2 ^ 144),
          Nat.mul_add_div (by norm_num : 0 < (2 : Nat) ^ 144),
          Nat.div_eq_of_lt hnR, Nat.add_zero]
      have hexp : (256 : Nat) ^ (32 - 1 - i) = 2 ^ 144 * 256 ^ (13 - i) := by
        interval_cases i <;> norm_num
      have hidx : 32 - 1 - (i + 18) = 13 - i := by omega
      rw [if_pos (by omega), hexp, ← Nat.div_div_eq_div_mul, hdiv, hidx]
    · rw [if_neg (by omega)]
      have hc : (2 : Nat) ^ 144 % (256 ^ (32 - 1 - i) * 256) = 0 := by
        interval_cases i <;> norm_num
      rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self n]
      congr 1
      rw [Nat.mul_add, Nat.mul_one, Nat.add_mod, Nat.mul_mod, hc]
      simp only [Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.mod_mod]

theorem encoded_packed (w : UInt256) (hw : w.toNat < 2 ^ 32)
    (i : Nat) (hi : i < 32) :
    (Data.Bytes.natToBytesPadded (packed w).toNat 32)[i]?.getD 0 =
      if 10 ≤ i ∧ i < 14 then
        (Data.Bytes.natToBytesPadded w.toNat 32)[i + 18]?.getD 0
      else (Data.Bytes.natToBytesPadded w.toNat 32)[i]?.getD 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi,
    packed_toNat w hw, byte_pack_nat _ _ hw hi]
  by_cases h : 10 ≤ i ∧ i < 14
  · rw [if_pos h, if_pos h,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega)]
  · rw [if_neg h, if_neg h,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]

theorem encoded_prefix_zero (w : UInt256) (hw : w.toNat < 2 ^ 32)
    (i : Nat) (hi : i < 28) :
    (Data.Bytes.natToBytesPadded w.toNat 32)[i]?.getD 0 = 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega)]
  have hp : (256 : Nat) ^ 4 ≤ 256 ^ (32 - 1 - i) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hlt : w.toNat < 256 ^ (32 - 1 - i) := by
    calc
      w.toNat < 2 ^ 32 := hw
      _ = 256 ^ 4 := by norm_num
      _ ≤ _ := hp
  rw [Nat.div_eq_of_lt hlt]
  rfl

/-- The next lower store may have any value, including an already packed value.
Only the four-byte gap exposed by dropping the middle store must be zero. -/
theorem three_store_merge (memory : ByteArray) (a : Nat) (w v : UInt256)
    (ha : 36 ≤ a) (hw : w.toNat < 2 ^ 32)
    (hgap : ∀ i, a - 4 ≤ i → i < a → memory[i]?.getD 0 = 0) :
    writeWord (writeWord (writeWord memory a w) (a - 18) w) (a - 36) v =
      writeWord (writeWord memory a (UInt256.mul w (UInt256.ofNat (2 ^ 144 + 1))))
        (a - 36) v := by
  change writeWord (writeWord (writeWord memory a w) (a - 18) w) (a - 36) v =
    writeWord (writeWord memory a (packed w)) (a - 36) v
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
        · rw [if_pos hin, encoded_packed w hw (i - a) (by omega)]
          by_cases hhi : 10 ≤ i - a ∧ i - a < 14
          · rw [if_pos hhi]
            congr 2
            omega
          · rw [if_neg hhi, encoded_prefix_zero w hw _ (by omega),
              encoded_prefix_zero w hw _ (by omega)]
        · rw [if_neg hin, encoded_prefix_zero w hw _ (by omega)]
          exact (hgap i (by omega) (by omega)).symm
      · rw [if_neg hmid]
        by_cases hin : a ≤ i ∧ i < a + 32
        · rw [if_pos hin, if_pos hin, encoded_packed w hw (i - a) (by omega),
            if_neg (by omega)]
        · rw [if_neg hin, if_neg hin]

#print axioms packed_toNat
#print axioms encoded_packed
#print axioms three_store_merge
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreMerge
