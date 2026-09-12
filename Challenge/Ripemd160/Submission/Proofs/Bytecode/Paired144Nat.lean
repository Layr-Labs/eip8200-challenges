import Init.Data.BitVec.Lemmas

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Nat

theorem div_pow_add_mul_pow (X Y k m : Nat) (hkm : k ≤ m) :
    (X + Y * 2 ^ m) / 2 ^ k = X / 2 ^ k + Y * 2 ^ (m - k) := by
  have h : 2 ^ m = 2 ^ (m - k) * 2 ^ k := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hkm]
  rw [h, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k)]

theorem mod_pow_add_mul_pow (X Y n w : Nat) (hn : w ≤ n) :
    (X + Y * 2 ^ n) % 2 ^ w = X % 2 ^ w := by
  have h : 2 ^ n = 2 ^ (n - w) * 2 ^ w := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hn]
  rw [h, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]

theorem mul_pow_div_pow (X d k : Nat) (hdk : d ≤ k) :
    X * 2 ^ d / 2 ^ k = X / 2 ^ (k - d) := by
  have h : 2 ^ k = 2 ^ (k - d) * 2 ^ d := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hdk]
  rw [h, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos d)]

theorem truncate_window (N k w b : Nat) (hkw : k + w ≤ b) :
    (N % 2 ^ b) / 2 ^ k % 2 ^ w = N / 2 ^ k % 2 ^ w := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.pow_add,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hkw), Nat.pow_add,
    Nat.mod_mul_right_div_self]

theorem div_pow_add_mul_pow_of_lt (X Y k m : Nat) (hX : X < 2 ^ m) :
    (X + Y * 2 ^ m) / 2 ^ (m + k) = Y / 2 ^ k := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hX, Nat.zero_add]

theorem rotate_toNat (a : BitVec 32) (r : Nat) (hr0 : 0 < r) (hr : r < 32) :
    (a.rotateLeft r).toNat = a.toNat * (2 ^ 32 + 1) / 2 ^ (32 - r) % 2 ^ 32 := by
  have hdup : (a ++ a).toNat = a.toNat * (2 ^ 32 + 1) := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt a.isLt,
      Nat.shiftLeft_eq, Nat.mul_add, Nat.mul_one]
  have hrot : (a ++ a).extractLsb' (32 - r) 32 = a.rotateLeft r := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have ht : 32 - r + i < 64 := by omega
    rw [BitVec.getLsbD_extractLsb', show decide (i < 32) = true from decide_eq_true hi,
      Bool.true_and, BitVec.getLsbD_append, BitVec.getLsbD_rotateLeft_of_le (by omega)]
    by_cases h : i < r
    · have hp : 32 - r + i < 32 := by omega
      simp [h, hp]
    · have hp : ¬ 32 - r + i < 32 := by omega
      have he : 32 - r + i - 32 = i - r := by omega
      simp [h, hp, he, hi]
  rw [← hrot, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, hdup]

#print axioms truncate_window
#print axioms rotate_toNat

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Nat
