import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactProduct
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Carry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Nat

set_option warningAsError true
set_option maxHeartbeats 500000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactRotation
open Paired144Core Paired144CompactGap Paired144CompactProduct

private theorem div_mod_low72 (x n : Nat) (hn : n + 32 ≤ 72) :
    x / 2 ^ n % 2 ^ 32 = (x % 2 ^ 72) / 2 ^ n % 2 ^ 32 := by
  exact (Paired144Nat.truncate_window x n 32 72 hn).symm

private theorem scaled_rotate_nat (a : BitVec 32) (u n : Nat)
    (hun : u < n) (hn : n < 32) :
    a.toNat * (2 ^ 32 + 1) * 2 ^ u / 2 ^ n % 2 ^ 32 =
      (a.rotateLeft (32 + u - n)).toNat := by
  have hr0 : 0 < 32 + u - n := by omega
  have hr : 32 + u - n < 32 := by omega
  have he : n - u = 32 - (32 + u - n) := by omega
  rw [Paired144Nat.rotate_toNat a _ hr0 hr,
    Paired144Nat.mul_pow_div_pow _ _ _ (by omega), he]

theorem low_shifted (a b : BitVec 32) (u v n : Nat)
    (hu : u ≤ 7) (hn0 : 8 ≤ n) (hn1 : n ≤ 31) :
    low (rawProduct a b u v >>> n) = a.rotateLeft (32 + u - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [low, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  rw [div_mod_low72 _ _ (by omega), rawProduct_low72_eq a b u v hu]
  exact scaled_rotate_nat a u n (by omega) (by omega)

theorem high_shifted (a b : BitVec 32) (u v n : Nat)
    (hu : u ≤ 7) (hv : v ≤ 7) (hn0 : 8 ≤ n) (hn1 : n ≤ 31) :
    high (rawProduct a b u v >>> n) = b.rotateLeft (32 + v - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [high, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ n) (2 ^ 144),
    ← Nat.div_div_eq_div_mul, rawProduct_high144_eq a b u v hu hv]
  exact scaled_rotate_nat b v n (by omega) (by omega)

/-- Both active cells and the addition of E are correct. The spacer bits are
permitted to remain dirty; only a proven zero bit is used to exclude a carry. -/
theorem normalize_shifted_add (a b e f : BitVec 32) (u v n : Nat)
    (hu : u ≤ 7) (hv : v ≤ 7) (hn0 : 8 ≤ n) (hn1 : n ≤ 31) :
    normalize ((rawProduct a b u v >>> n) + pack e f) =
      pack (a.rotateLeft (32 + u - n) + e)
        (b.rotateLeft (32 + v - n) + f) := by
  rw [Paired144Carry.normalize_add_pack _ e f (71 - n) (by omega) (by omega)
    (shiftedProduct_gap a b u v n hu (by omega)),
    low_shifted a b u v n hu hn0 hn1, high_shifted a b u v n hu hv hn0 hn1]

#print axioms low_shifted
#print axioms high_shifted
#print axioms normalize_shifted_add
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactRotation
