import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Nat
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Core

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144LegacyProduct

open Paired144Nat Paired144Core

private theorem low_shift_nat (x : BitVec 256) (n : Nat) :
    (low (x >>> n)).toNat = x.toNat / 2 ^ n % 2 ^ 32 := by
  simp only [low, BitVec.extractLsb'_toNat, Nat.pow_zero, Nat.div_one,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem high_shift_nat (x : BitVec 256) (n : Nat) :
    (high (x >>> n)).toNat = x.toNat / 2 ^ (n + 144) % 2 ^ 32 := by
  simp only [high, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]

def coefficient : BitVec 256 := BitVec.ofNat 256 ((2 ^ 32 + 1) * (2 ^ 6 + 2 ^ 72))

def scaled (a b : BitVec 32) (u v : Nat) : BitVec 256 :=
  (BitVec.ofNat 256 a.toNat <<< u) + (BitVec.ofNat 256 b.toNat <<< (144 + v))

def rawProduct (a b : BitVec 32) (u v : Nat) : BitVec 256 :=
  scaled a b u v * coefficient

def natProduct (a b u v : Nat) : Nat :=
  (a * 2 ^ u + b * 2 ^ (144 + v)) * ((2 ^ 32 + 1) * (2 ^ 6 + 2 ^ 72))

def lowChunk (a u : Nat) : Nat := a * (2 ^ 32 + 1) * 2 ^ u * (2 ^ 6 + 2 ^ 72)

def highChunk (b v : Nat) : Nat := b * (2 ^ 32 + 1) * 2 ^ v * (1 + 2 ^ 66)

private theorem shifted_mul_toNat (a b : BitVec 32) (c : BitVec 256) (u v : Nat) :
    (((BitVec.ofNat 256 a.toNat <<< u) +
      (BitVec.ofNat 256 b.toNat <<< v)) * c).toNat =
      ((a.toNat * 2 ^ u + b.toNat * 2 ^ v) * c.toNat) % 2 ^ 256 := by
  simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.add_mod_mod, Nat.mod_add_mod,
    Nat.mod_mul_mod]

private theorem coefficient_toNat : coefficient.toNat = (2 ^ 32 + 1) * (2 ^ 6 + 2 ^ 72) := by
  decide

theorem rawProduct_toNat (a b : BitVec 32) (u v : Nat) :
    (rawProduct a b u v).toNat = natProduct a.toNat b.toNat u v % 2 ^ 256 := by
  unfold rawProduct scaled
  rw [shifted_mul_toNat, coefficient_toNat]
  rfl

theorem natProduct_chunks (a b u v : Nat) :
    natProduct a b u v = lowChunk a u + highChunk b v * 2 ^ 150 := by
  unfold natProduct lowChunk highChunk
  rw [Nat.add_mul]
  refine congr (congrArg Nat.add ?_) ?_
  · ac_rfl
  · rw [Nat.pow_add]
    have hc : 2 ^ 144 * (2 ^ 32 + 1) * (2 ^ 6 + 2 ^ 72) =
        (2 ^ 32 + 1) * (1 + 2 ^ 66) * 2 ^ 150 := by decide
    calc
      _ = (b * 2 ^ v) * (2 ^ 144 * (2 ^ 32 + 1) * (2 ^ 6 + 2 ^ 72)) := by ac_rfl
      _ = (b * 2 ^ v) * ((2 ^ 32 + 1) * (1 + 2 ^ 66) * 2 ^ 150) := by rw [hc]
      _ = _ := by ac_rfl

theorem lowChunk_lt (a : BitVec 32) (u : Nat) (hu : u ≤ 10) :
    lowChunk a.toNat u < 2 ^ 149 := by
  have ha : a.toNat ≤ 2 ^ 32 - 1 := Nat.le_sub_one_of_lt a.isLt
  have hp : 2 ^ u ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hu
  calc
    lowChunk a.toNat u ≤ (2 ^ 32 - 1) * (2 ^ 32 + 1) * 2 ^ 10 * (2 ^ 6 + 2 ^ 72) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_right _ ha) hp)
    _ < 2 ^ 149 := by decide

private theorem gap149_of_residue (x : BitVec 256) (y : Nat)
    (hmod : x.toNat % 2 ^ 150 = y) (hy : y < 2 ^ 149) : x.getLsbD 149 = false := by
  rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  apply decide_eq_false_iff_not.mpr
  simp only [Nat.reducePow] at *
  omega

theorem rawProduct_gap149 (a b : BitVec 32) (u v : Nat) (hu : u ≤ 10) :
    (rawProduct a b u v).getLsbD 149 = false := by
  have hlow := lowChunk_lt a u hu
  have hmod : (rawProduct a b u v).toNat % 2 ^ 150 = lowChunk a.toNat u := by
    rw [rawProduct_toNat, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 150 ≤ 256)),
      natProduct_chunks, mod_pow_add_mul_pow _ _ 150 150 (by decide)]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hlow (by decide))
  exact gap149_of_residue _ _ hmod hlow

theorem shiftedProduct_gap (a b : BitVec 32) (u v n : Nat)
    (hu : u ≤ 10) (hn : n ≤ 149) :
    (rawProduct a b u v >>> n).getLsbD (149 - n) = false := by
  rw [BitVec.getLsbD_ushiftRight]
  have hindex : n + (149 - n) = 149 := by omega
  rw [hindex]
  exact rawProduct_gap149 a b u v hu

theorem low_shift_toNat (a b : BitVec 32) (u v n : Nat)
    (hu : u ≤ 10) (hn0 : 23 ≤ n) (hn : n ≤ 33) :
    (low (rawProduct a b u v >>> n)).toNat =
      a.toNat * (2 ^ 32 + 1) / 2 ^ (n - 6 - u) % 2 ^ 32 := by
  rw [low_shift_nat]
  rw [rawProduct_toNat, truncate_window _ n 32 256 (by omega), natProduct_chunks,
    div_pow_add_mul_pow _ _ n 150 (by omega), mod_pow_add_mul_pow _ _ _ 32 (by omega)]
  unfold lowChunk
  rw [Nat.mul_add, div_pow_add_mul_pow _ _ n 72 (by omega),
    mod_pow_add_mul_pow _ _ _ 32 (by omega), mul_pow_div_pow _ 6 n (by omega),
    mul_pow_div_pow _ u (n - 6) (by omega)]

theorem high_shift_toNat (a b : BitVec 32) (u v n : Nat)
    (hu : u ≤ 10) (hv : v ≤ 10) (hn0 : 23 ≤ n) (hn : n ≤ 33) :
    (high (rawProduct a b u v >>> n)).toNat =
      b.toNat * (2 ^ 32 + 1) / 2 ^ (n - 6 - v) % 2 ^ 32 := by
  rw [high_shift_nat]
  rw [rawProduct_toNat, truncate_window _ (n + 144) 32 256 (by omega), natProduct_chunks]
  have he : n + 144 = 150 + (n - 6) := by omega
  rw [he, div_pow_add_mul_pow_of_lt _ _ (n - 6) 150
    (Nat.lt_trans (lowChunk_lt a u hu) (by decide))]
  unfold highChunk
  rw [Nat.mul_add, Nat.mul_one, div_pow_add_mul_pow _ _ (n - 6) 66 (by omega),
    mod_pow_add_mul_pow _ _ _ 32 (by omega), mul_pow_div_pow _ v (n - 6) (by omega)]

#print axioms rawProduct_toNat
#print axioms rawProduct_gap149
#print axioms shiftedProduct_gap
#print axioms low_shift_toNat
#print axioms high_shift_toNat

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144LegacyProduct
