import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Rotate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Boolean
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80SumsBase
import Mathlib.Tactic.Ring

set_option warningAsError true

/-!
# MUL-scale dual rotation

Before the shared `factor = 2^32 + 1` multiply, the lane that needs the larger
rotation is pre-scaled by `2^d`, where `d` is the difference of the two
rotation amounts.  A single shift by `32 - min r s` then rotates both lanes.
Only the two 32-bit cells of a packed word are inspected; the spacer bits
carry garbage, except bit 48, which is proven zero so that the following
addition cannot carry into the high lane.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80ScaledRotate

open Paired80Core Paired80Product Paired80Rotate Paired80Boolean

/-- Pre-scale the low lane by `2^d`: `x + (x & lowerMask) * (2^d - 1)`. -/
def scaleLow (x : BitVec 256) (d : Nat) : BitVec 256 :=
  BitVec.ofNat 256 (2 ^ d - 1) * (lowerMask &&& x) + x

/-- Pre-scale the high lane by `2^d`: `x + (x & upperMask) * (2^d - 1)`. -/
def scaleHigh (x : BitVec 256) (d : Nat) : BitVec 256 :=
  BitVec.ofNat 256 (2 ^ d - 1) * (upperMask &&& x) + x

theorem lowerMask_and_pack (a b : BitVec 32) : lowerMask &&& pack a b = pack a 0#32 := by
  rw [lowerMask, pack_and, BitVec.allOnes_and, BitVec.zero_and]

theorem upperMask_and_pack (a b : BitVec 32) : upperMask &&& pack a b = pack 0#32 b := by
  rw [upperMask, pack_and, BitVec.zero_and, BitVec.allOnes_and]

theorem factor_toNat : factor.toNat = 2 ^ 32 + 1 := by decide

theorem toNat_pack_zero_right (a : BitVec 32) : (pack a 0#32).toNat = a.toNat := by
  rw [pack_toNat]
  simp

theorem toNat_pack_zero_left (b : BitVec 32) : (pack 0#32 b).toNat = b.toNat * 2 ^ 80 := by
  rw [pack_toNat]
  simp

/-! ## Natural-number facts -/

theorem scale_nat (P A : Nat) (hP : 0 < P) : (P - 1) * A + A = P * A := by
  have h1 : (P - 1) * A = P * A - A := by rw [Nat.sub_mul, Nat.one_mul]
  rw [h1, Nat.sub_add_cancel (Nat.le_mul_of_pos_left A hP)]

theorem div_pow_add_mul_pow (X Y k m : Nat) (hkm : k ≤ m) :
    (X + Y * 2 ^ m) / 2 ^ k = X / 2 ^ k + Y * 2 ^ (m - k) := by
  have h : 2 ^ m = 2 ^ (m - k) * 2 ^ k := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hkm]
  rw [h, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k)]

theorem mod_pow32_add_mul_pow (X Y n : Nat) (hn : 32 ≤ n) :
    (X + Y * 2 ^ n) % 2 ^ 32 = X % 2 ^ 32 := by
  have h : 2 ^ n = 2 ^ (n - 32) * 2 ^ 32 := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hn]
  rw [h, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]

theorem mul_pow_div_pow (X d k : Nat) (hdk : d ≤ k) :
    X * 2 ^ d / 2 ^ k = X / 2 ^ (k - d) := by
  have h : 2 ^ k = 2 ^ (k - d) * 2 ^ d := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hdk]
  rw [h, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos d)]

theorem div_pow_add_mul_pow80 (X Y k : Nat) (hX : X < 2 ^ 80) :
    (X + Y * 2 ^ 80) / 2 ^ (k + 80) = Y / 2 ^ k := by
  rw [Nat.pow_add, Nat.mul_comm (2 ^ k), ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos 80), Nat.div_eq_of_lt hX, Nat.zero_add]

theorem testBit_add_mul_pow80 (X Y i : Nat) (hi : i < 80) (hX : X < 2 ^ i) :
    (X + Y * 2 ^ 80).testBit i = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq, div_pow_add_mul_pow X Y i 80 (by omega),
    Nat.div_eq_of_lt hX, Nat.zero_add]
  have h : 2 ^ (80 - i) = 2 ^ (79 - i) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have h2 : Y * 2 ^ (80 - i) % 2 = 0 := by
    rw [h, ← Nat.mul_assoc]
    omega
  rw [h2]
  decide

/-! ## Exact products of the scaled packed word -/

theorem toNat_le_pred (a : BitVec 32) : a.toNat ≤ 2 ^ 32 - 1 := Nat.le_sub_one_of_lt a.isLt

theorem pow_le_of_le_31 (d : Nat) (hd : d ≤ 31) : 2 ^ d ≤ 2 ^ 31 :=
  Nat.pow_le_pow_right (by decide) hd

theorem pred_pow_le (d : Nat) (hd : d ≤ 31) : 2 ^ d - 1 ≤ 2 ^ 31 :=
  Nat.le_trans (Nat.sub_le _ _) (pow_le_of_le_31 d hd)

theorem pack_factor_toNat (a b : BitVec 32) :
    (pack a b * factor).toNat = (a.toNat + b.toNat * 2 ^ 80) * (2 ^ 32 + 1) := by
  rw [BitVec.toNat_mul, pack_toNat, factor_toNat]
  apply Nat.mod_eq_of_lt
  calc (a.toNat + b.toNat * 2 ^ 80) * (2 ^ 32 + 1)
      ≤ ((2 ^ 32 - 1) + (2 ^ 32 - 1) * 2 ^ 80) * (2 ^ 32 + 1) :=
        Nat.mul_le_mul_right _
          (Nat.add_le_add (toNat_le_pred a) (Nat.mul_le_mul_right _ (toNat_le_pred b)))
    _ < 2 ^ 256 := by decide

theorem scaleLow_toNat (a b : BitVec 32) (d : Nat) (hd : d ≤ 31) :
    (scaleLow (pack a b) d).toNat = a.toNat * 2 ^ d + b.toNat * 2 ^ 80 := by
  rw [scaleLow, lowerMask_and_pack, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    toNat_pack_zero_right, pack_toNat]
  have h1 : (2 ^ d - 1) % 2 ^ 256 = 2 ^ d - 1 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (pred_pow_le d hd) (by decide))
  have h2 : (2 ^ d - 1) * a.toNat % 2 ^ 256 = (2 ^ d - 1) * a.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
      (Nat.mul_le_mul (pred_pow_le d hd) (toNat_le_pred a)) (by decide))
  rw [h1, h2, ← Nat.add_assoc, scale_nat _ _ (Nat.two_pow_pos d), Nat.mul_comm (2 ^ d)]
  apply Nat.mod_eq_of_lt
  calc a.toNat * 2 ^ d + b.toNat * 2 ^ 80
      ≤ (2 ^ 32 - 1) * 2 ^ 31 + (2 ^ 32 - 1) * 2 ^ 80 :=
        Nat.add_le_add (Nat.mul_le_mul (toNat_le_pred a) (pow_le_of_le_31 d hd))
          (Nat.mul_le_mul_right _ (toNat_le_pred b))
    _ < 2 ^ 256 := by decide

theorem scaleHigh_toNat (a b : BitVec 32) (d : Nat) (hd : d ≤ 31) :
    (scaleHigh (pack a b) d).toNat = a.toNat + b.toNat * 2 ^ 80 * 2 ^ d := by
  rw [scaleHigh, upperMask_and_pack, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    toNat_pack_zero_left, pack_toNat]
  have h1 : (2 ^ d - 1) % 2 ^ 256 = 2 ^ d - 1 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (pred_pow_le d hd) (by decide))
  have h2 : (2 ^ d - 1) * (b.toNat * 2 ^ 80) % 2 ^ 256 = (2 ^ d - 1) * (b.toNat * 2 ^ 80) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
      (Nat.mul_le_mul (pred_pow_le d hd) (Nat.mul_le_mul_right _ (toNat_le_pred b)))
      (by decide))
  have e : (2 ^ d - 1) * (b.toNat * 2 ^ 80) + (a.toNat + b.toNat * 2 ^ 80) =
      a.toNat + ((2 ^ d - 1) * (b.toNat * 2 ^ 80) + b.toNat * 2 ^ 80) := by ring
  rw [h1, h2, e, scale_nat _ _ (Nat.two_pow_pos d), Nat.mul_comm (2 ^ d)]
  apply Nat.mod_eq_of_lt
  calc a.toNat + b.toNat * 2 ^ 80 * 2 ^ d
      ≤ (2 ^ 32 - 1) + (2 ^ 32 - 1) * 2 ^ 80 * 2 ^ 31 :=
        Nat.add_le_add (toNat_le_pred a)
          (Nat.mul_le_mul (Nat.mul_le_mul_right _ (toNat_le_pred b)) (pow_le_of_le_31 d hd))
    _ < 2 ^ 256 := by decide

theorem scaleLow_product_toNat (a b : BitVec 32) (d : Nat) (hd : d ≤ 31) :
    (scaleLow (pack a b) d * factor).toNat =
      a.toNat * (2 ^ 32 + 1) * 2 ^ d + (b.toNat * (2 ^ 32 + 1)) * 2 ^ 80 := by
  rw [BitVec.toNat_mul, scaleLow_toNat a b d hd, factor_toNat]
  have e : (a.toNat * 2 ^ d + b.toNat * 2 ^ 80) * (2 ^ 32 + 1) =
      a.toNat * (2 ^ 32 + 1) * 2 ^ d + (b.toNat * (2 ^ 32 + 1)) * 2 ^ 80 := by ring
  rw [e]
  apply Nat.mod_eq_of_lt
  calc a.toNat * (2 ^ 32 + 1) * 2 ^ d + (b.toNat * (2 ^ 32 + 1)) * 2 ^ 80
      ≤ (2 ^ 32 - 1) * (2 ^ 32 + 1) * 2 ^ 31 + ((2 ^ 32 - 1) * (2 ^ 32 + 1)) * 2 ^ 80 :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.mul_le_mul_right _ (toNat_le_pred a)) (pow_le_of_le_31 d hd))
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (toNat_le_pred b)))
    _ < 2 ^ 256 := by decide

theorem scaleHigh_product_toNat (a b : BitVec 32) (d : Nat) (hd : d ≤ 31) :
    (scaleHigh (pack a b) d * factor).toNat =
      a.toNat * (2 ^ 32 + 1) + (b.toNat * (2 ^ 32 + 1) * 2 ^ d) * 2 ^ 80 := by
  rw [BitVec.toNat_mul, scaleHigh_toNat a b d hd, factor_toNat]
  have e : (a.toNat + b.toNat * 2 ^ 80 * 2 ^ d) * (2 ^ 32 + 1) =
      a.toNat * (2 ^ 32 + 1) + (b.toNat * (2 ^ 32 + 1) * 2 ^ d) * 2 ^ 80 := by ring
  rw [e]
  apply Nat.mod_eq_of_lt
  calc a.toNat * (2 ^ 32 + 1) + (b.toNat * (2 ^ 32 + 1) * 2 ^ d) * 2 ^ 80
      ≤ (2 ^ 32 - 1) * (2 ^ 32 + 1) + ((2 ^ 32 - 1) * (2 ^ 32 + 1) * 2 ^ 31) * 2 ^ 80 :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (toNat_le_pred a))
          (Nat.mul_le_mul_right _
            (Nat.mul_le_mul (Nat.mul_le_mul_right _ (toNat_le_pred b)) (pow_le_of_le_31 d hd)))
    _ < 2 ^ 256 := by decide

/-! ## Lane extraction -/

theorem toNat_low (x : BitVec 256) : (low x).toNat = x.toNat % 2 ^ 32 := by
  simp only [low, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

theorem toNat_high (x : BitVec 256) : (high x).toNat = x.toNat / 2 ^ 80 % 2 ^ 32 := by
  simp only [high, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem toNat_shift (x : BitVec 256) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem aF_lt_64 (a : BitVec 32) : a.toNat * (2 ^ 32 + 1) < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (toNat_le_pred a)) (by decide)

theorem aF_lt_80 (a : BitVec 32) : a.toNat * (2 ^ 32 + 1) < 2 ^ 80 :=
  Nat.lt_of_lt_of_le (aF_lt_64 a) (by decide)

theorem pack_factor_low_toNat (a b : BitVec 32) (k : Nat) (hk : k ≤ 48) :
    (low ((pack a b * factor) >>> k)).toNat = a.toNat * (2 ^ 32 + 1) / 2 ^ k % 2 ^ 32 := by
  rw [toNat_low, toNat_shift, pack_factor_toNat]
  have e : (a.toNat + b.toNat * 2 ^ 80) * (2 ^ 32 + 1) =
      a.toNat * (2 ^ 32 + 1) + (b.toNat * (2 ^ 32 + 1)) * 2 ^ 80 := by ring
  rw [e, div_pow_add_mul_pow _ _ k 80 (by omega), mod_pow32_add_mul_pow _ _ _ (by omega)]

theorem pack_factor_high_toNat (a b : BitVec 32) (k : Nat) :
    (high ((pack a b * factor) >>> k)).toNat = b.toNat * (2 ^ 32 + 1) / 2 ^ k % 2 ^ 32 := by
  rw [toNat_high, toNat_shift, pack_factor_toNat, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have e : (a.toNat + b.toNat * 2 ^ 80) * (2 ^ 32 + 1) =
      a.toNat * (2 ^ 32 + 1) + (b.toNat * (2 ^ 32 + 1)) * 2 ^ 80 := by ring
  rw [e, div_pow_add_mul_pow80 _ _ k (aF_lt_80 a)]

/-! ## The low lane is pre-scaled (`s < r`) -/

theorem low_scaleLow (a b : BitVec 32) (r s : Nat)
    (hs0 : 0 < s) (hsr : s < r) (hr : r < 17) :
    low ((scaleLow (pack a b) (r - s) * factor) >>> (32 - s)) = a.rotateLeft r := by
  rw [← low_rotate_product a b r (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [pack_factor_low_toNat a b (32 - r) (by omega), toNat_low, toNat_shift,
    scaleLow_product_toNat a b (r - s) (by omega),
    div_pow_add_mul_pow _ _ (32 - s) 80 (by omega), mod_pow32_add_mul_pow _ _ _ (by omega),
    mul_pow_div_pow _ _ _ (by omega)]
  have e : 32 - s - (r - s) = 32 - r := by omega
  rw [e]

theorem high_scaleLow (a b : BitVec 32) (r s : Nat)
    (hs0 : 0 < s) (hs : s < 17) (hsr : s < r) (hr : r < 17) :
    high ((scaleLow (pack a b) (r - s) * factor) >>> (32 - s)) = b.rotateLeft s := by
  rw [← high_rotate_product a b s hs0 (by omega)]
  apply BitVec.eq_of_toNat_eq
  have hX : a.toNat * (2 ^ 32 + 1) * 2 ^ (r - s) < 2 ^ 80 :=
    Nat.lt_of_le_of_lt
      (Nat.mul_le_mul (Nat.le_of_lt (aF_lt_64 a)) (show 2 ^ (r - s) ≤ 2 ^ 15 from Nat.pow_le_pow_right (by decide) (by omega)))
      (by decide)
  rw [pack_factor_high_toNat a b (32 - s), toNat_high, toNat_shift,
    scaleLow_product_toNat a b (r - s) (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add,
    div_pow_add_mul_pow80 _ _ _ hX]

theorem gap_scaleLow (a b : BitVec 32) (r s : Nat)
    (hs0 : 0 < s) (hsr : s < r) (hr : r < 17) :
    ((scaleLow (pack a b) (r - s) * factor) >>> (32 - s)).getLsbD 48 = false := by
  rw [BitVec.getLsbD_ushiftRight, ← BitVec.testBit_toNat,
    scaleLow_product_toNat a b (r - s) (by omega)]
  apply testBit_add_mul_pow80 _ _ _ (by omega)
  have hpow : 2 ^ (r - s) ≤ 2 ^ (16 - s) := Nat.pow_le_pow_right (by decide) (by omega)
  calc a.toNat * (2 ^ 32 + 1) * 2 ^ (r - s)
      < 2 ^ 64 * 2 ^ (16 - s) :=
        Nat.mul_lt_mul_of_lt_of_le (aF_lt_64 a) hpow (Nat.two_pow_pos _)
    _ = 2 ^ (32 - s + 48) := by
      rw [← Nat.pow_add]
      congr 1
      omega

/-! ## The high lane is pre-scaled (`r < s`) -/

theorem low_scaleHigh (a b : BitVec 32) (r s : Nat)
    (hr0 : 0 < r) (hrs : r < s) (hs : s < 17) :
    low ((scaleHigh (pack a b) (s - r) * factor) >>> (32 - r)) = a.rotateLeft r := by
  rw [← low_rotate_product a b r hr0 (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [pack_factor_low_toNat a b (32 - r) (by omega), toNat_low, toNat_shift,
    scaleHigh_product_toNat a b (s - r) (by omega),
    div_pow_add_mul_pow _ _ (32 - r) 80 (by omega), mod_pow32_add_mul_pow _ _ _ (by omega)]

theorem high_scaleHigh (a b : BitVec 32) (r s : Nat)
    (hr0 : 0 < r) (hrs : r < s) (hs : s < 17) :
    high ((scaleHigh (pack a b) (s - r) * factor) >>> (32 - r)) = b.rotateLeft s := by
  rw [← high_rotate_product a b s (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [pack_factor_high_toNat a b (32 - s), toNat_high, toNat_shift,
    scaleHigh_product_toNat a b (s - r) (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add,
    div_pow_add_mul_pow80 _ _ _ (aF_lt_80 a), mul_pow_div_pow _ _ _ (by omega)]
  have e : 32 - r - (s - r) = 32 - s := by omega
  rw [e]

theorem gap_scaleHigh (a b : BitVec 32) (r s : Nat)
    (hr0 : 0 < r) (hrs : r < s) (hs : s < 17) :
    ((scaleHigh (pack a b) (s - r) * factor) >>> (32 - r)).getLsbD 48 = false := by
  rw [BitVec.getLsbD_ushiftRight, ← BitVec.testBit_toNat,
    scaleHigh_product_toNat a b (s - r) (by omega)]
  apply testBit_add_mul_pow80 _ _ _ (by omega)
  calc a.toNat * (2 ^ 32 + 1) < 2 ^ 64 := aF_lt_64 a
    _ ≤ 2 ^ (32 - r + 48) := Nat.pow_le_pow_right (by decide) (by omega)

#print axioms low_scaleLow
#print axioms high_scaleLow
#print axioms gap_scaleLow
#print axioms low_scaleHigh
#print axioms high_scaleHigh
#print axioms gap_scaleHigh

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80ScaledRotate
