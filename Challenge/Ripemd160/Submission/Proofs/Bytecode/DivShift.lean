import Challenge.EvmProof.Word

set_option warningAsError true

/-!
# Division by a power of two is a logical right shift

The rotation fold multiplies a masked 32-bit word by `F = 2^32 + 1` and then
extracts the rotated result with a right shift.  The shift amount arrives from
the caller, below the product, so `SHR` needs a `SWAP1` first.  `DIV` reads its
operands in the opposite order, so passing `2 ^ (32 - r)` instead of `32 - r`
removes that swap.  This module proves the two are the same operation.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DivShift

open EvmSemantics

/-- `UInt256.ofNat (2 ^ k)` is nonzero for `k < 256`. -/
theorem ofNat_two_pow_toNat {k : Nat} (hk : k < 256) :
    (UInt256.ofNat (2 ^ k)).toNat = 2 ^ k := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right Nat.one_lt_two hk)

/-- `DIV` by `2 ^ k` computes the same natural number as `SHR` by `k`. -/
theorem div_two_pow_toNat (a : UInt256) {k : Nat} (hk : k < 256) :
    (UInt256.div a (UInt256.ofNat (2 ^ k))).toNat = a.toNat >>> k := by
  have hval : (UInt256.ofNat (2 ^ k)).val.val = 2 ^ k := ofNat_two_pow_toNat hk
  have hpos : (0 : Nat) < 2 ^ k := by positivity
  have hne : (UInt256.ofNat (2 ^ k)).val.val ≠ 0 := by
    rw [hval]; exact hpos.ne'
  unfold UInt256.div
  rw [if_neg hne]
  show a.val.val / (UInt256.ofNat (2 ^ k)).val.val = a.toNat >>> k
  rw [hval, Nat.shiftRight_eq_div_pow]
  rfl

/-- The operand-order-swapped rotation extraction agrees with `SHR`. -/
theorem div_two_pow_eq_shiftRight (a : UInt256) {k : Nat} (hk : k < 256) :
    UInt256.div a (UInt256.ofNat (2 ^ k)) =
      UInt256.shiftRight a (UInt256.ofNat k) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [div_two_pow_toNat a hk,
    Challenge.EvmProof.Word.shiftRight_toNat a hk]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DivShift
