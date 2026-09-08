import Challenge.EvmProof.Word

set_option warningAsError true

/-!
# Exact nibble addressing under a modular exponent-word shift

The lookup mask is `15 << 5`. Modulo-2^256 truncation after left shifts cannot
change a nibble whose four selected bits remain inside the word. These lemmas
cover every such shift and digit, rather than particular exponent values.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineBits

open EvmSemantics

theorem mask480_nat (value : Nat) :
    value &&& 480 = ((value >>> 5) % 16) <<< 5 := by
  have hmask : (480 : Nat) = (2 ^ 4 - 1) <<< 5 := by decide
  rw [hmask, ← Nat.and_two_pow_sub_one_eq_mod (value >>> 5) 4]
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : 5 ≤ bit
  · simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      hbit, decide_true, Bool.true_and]
    rw [show 5 + (bit - 5) = bit by omega]
  · simp only [Nat.testBit_and, Nat.testBit_shiftLeft, hbit,
      decide_false, Bool.false_and, Bool.and_false]

theorem shifted_nibble_nat (value shift offset : Nat)
    (hshift : shift ≤ offset) (hbits : offset + 4 ≤ 256) :
    ((((value <<< shift) % 2 ^ 256) >>> offset) % 16) =
      (value >>> (offset - shift)) % 16 := by
  change ((((value <<< shift) % 2 ^ 256) >>> offset) % 2 ^ 4) =
    (value >>> (offset - shift)) % 2 ^ 4
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit < 4
  · have hin : offset + bit < 256 := by omega
    have hge : shift ≤ offset + bit := by omega
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      Nat.testBit_shiftLeft, hbit, hin, hge, decide_true, Bool.true_and]
    congr 1
    omega
  · simp only [Nat.testBit_mod_two_pow, hbit, decide_false, Bool.false_and]

theorem shiftLeft_toNat_mod (value : UInt256) (shift : Nat) (hshift : shift < 256) :
    (UInt256.shiftLeft value (UInt256.ofNat shift)).toNat =
      (value.toNat <<< shift) % 2 ^ 256 := by
  have hword : (UInt256.ofNat shift).toNat = shift := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hshift (by norm_num))]
  unfold UInt256.shiftLeft
  rw [hword, if_neg (by omega), Challenge.EvmProof.Word.word_toNat_ofNat]
  change ((value.toNat <<< shift) % 2 ^ 256) % 2 ^ 256 = _
  rw [Nat.mod_mod]

def lookupAddress (value : UInt256) (shift : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight value (UInt256.ofNat shift)) (UInt256.ofNat 480)

theorem lookupAddress_toNat (value : UInt256) (shift : Nat) (hshift : shift < 256) :
    (lookupAddress value shift).toNat =
      32 * ((value.toNat >>> (shift + 5)) % 16) := by
  rw [lookupAddress, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.shiftRight_toNat value hshift,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num only [Nat.reducePow, Nat.reduceMod]
  rw [mask480_nat, ← Nat.shiftRight_add, Nat.shiftLeft_eq]
  norm_num only [Nat.reducePow]
  exact Nat.mul_comm _ 32

/-- An exponent shifted by `processed` nibbles exposes the next nine lookup
addresses using the three physical groups' shifts 247,243,...,215. -/
theorem shifted_lookupAddress (exponent : UInt256) (processed index : Nat)
    (hindex : index < 9) (hinside : processed + index < 64) :
    (lookupAddress
      (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed)))
      (247 - 4 * index)).toNat =
      32 * (exponent.toNat / 16 ^ (63 - (processed + index)) % 16) := by
  rw [lookupAddress_toNat _ _ (by omega), shiftLeft_toNat_mod _ _ (by omega)]
  have hshift : 4 * processed ≤ 247 - 4 * index + 5 := by omega
  have hbits : 247 - 4 * index + 5 + 4 ≤ 256 := by omega
  rw [shifted_nibble_nat exponent.toNat (4 * processed)
    (247 - 4 * index + 5) hshift hbits,
    show 247 - 4 * index + 5 - 4 * processed =
      4 * (63 - (processed + index)) by omega,
    Nat.shiftRight_eq_div_pow]
  have hpow (n : Nat) : (2 : Nat) ^ (4 * n) = 16 ^ n := by
    rw [Nat.pow_mul]
  rw [hpow]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineBits
