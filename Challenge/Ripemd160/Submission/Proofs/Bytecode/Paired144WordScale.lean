import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144LegacyProduct
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordScale
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144WordRound
theorem pack_and (a b c d : BitVec 32) :
    pack a b &&& pack c d = pack (a &&& c) (b &&& d) := by
  unfold pack
  rw [BitVec.and_append (x₁ := b.setWidth 112) (x₂ := d.setWidth 112)
    (y₁ := a.setWidth 144) (y₂ := c.setWidth 144)]
  rw [BitVec.setWidth_and, BitVec.setWidth_and]

def upperMask : BitVec 256 := pack 0#32 (BitVec.allOnes 32)
def lowerMask : BitVec 256 := pack (BitVec.allOnes 32) 0#32
def scaleLow (x : BitVec 256) (d : Nat) : BitVec 256 :=
  BitVec.ofNat 256 (2 ^ d - 1) * (lowerMask &&& x) + x

/-- Pre-scale the high lane by `2^d`: `x + (x & upperMask) * (2^d - 1)`. -/
def scaleHigh (x : BitVec 256) (d : Nat) : BitVec 256 :=
  BitVec.ofNat 256 (2 ^ d - 1) * (upperMask &&& x) + x

theorem lowerMask_and_pack (a b : BitVec 32) : lowerMask &&& pack a b = pack a 0#32 := by
  rw [lowerMask, pack_and, BitVec.allOnes_and, BitVec.zero_and]

theorem upperMask_and_pack (a b : BitVec 32) : upperMask &&& pack a b = pack 0#32 b := by
  rw [upperMask, pack_and, BitVec.zero_and, BitVec.allOnes_and]

theorem toNat_pack_zero_right (a : BitVec 32) : (pack a 0#32).toNat = a.toNat := by
  rw [pack_toNat]
  simp

theorem toNat_pack_zero_left (b : BitVec 32) : (pack 0#32 b).toNat = b.toNat * 2 ^ 144 := by
  rw [pack_toNat]
  simp

/-! ## Natural-number facts -/

theorem scale_nat (P A : Nat) (hP : 0 < P) : (P - 1) * A + A = P * A := by
  have h1 : (P - 1) * A = P * A - A := by rw [Nat.sub_mul, Nat.one_mul]
  rw [h1, Nat.sub_add_cancel (Nat.le_mul_of_pos_left A hP)]

theorem toNat_le_pred (a : BitVec 32) : a.toNat ≤ 2 ^ 32 - 1 := Nat.le_sub_one_of_lt a.isLt

theorem pow_le_of_le_31 (d : Nat) (hd : d ≤ 31) : 2 ^ d ≤ 2 ^ 31 :=
  Nat.pow_le_pow_right (by decide) hd

theorem pred_pow_le (d : Nat) (hd : d ≤ 31) : 2 ^ d - 1 ≤ 2 ^ 31 :=
  Nat.le_trans (Nat.sub_le _ _) (pow_le_of_le_31 d hd)

theorem scaleLow_toNat (a b : BitVec 32) (d : Nat) (hd : d ≤ 31) :
    (scaleLow (pack a b) d).toNat = a.toNat * 2 ^ d + b.toNat * 2 ^ 144 := by
  rw [scaleLow, lowerMask_and_pack, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    toNat_pack_zero_right, pack_toNat]
  have h1 : (2 ^ d - 1) % 2 ^ 256 = 2 ^ d - 1 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (pred_pow_le d hd) (by decide))
  have h2 : (2 ^ d - 1) * a.toNat % 2 ^ 256 = (2 ^ d - 1) * a.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
      (Nat.mul_le_mul (pred_pow_le d hd) (toNat_le_pred a)) (by decide))
  rw [h1, h2, ← Nat.add_assoc, scale_nat _ _ (Nat.two_pow_pos d), Nat.mul_comm (2 ^ d)]
  apply Nat.mod_eq_of_lt
  calc a.toNat * 2 ^ d + b.toNat * 2 ^ 144
      ≤ (2 ^ 32 - 1) * 2 ^ 31 + (2 ^ 32 - 1) * 2 ^ 144 :=
        Nat.add_le_add (Nat.mul_le_mul (toNat_le_pred a) (pow_le_of_le_31 d hd))
          (Nat.mul_le_mul_right _ (toNat_le_pred b))
    _ < 2 ^ 256 := by decide

theorem scaleHigh_toNat (a b : BitVec 32) (d : Nat) (hd : d ≤ 31) :
    (scaleHigh (pack a b) d).toNat = a.toNat + b.toNat * 2 ^ 144 * 2 ^ d := by
  rw [scaleHigh, upperMask_and_pack, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    toNat_pack_zero_left, pack_toNat]
  have h1 : (2 ^ d - 1) % 2 ^ 256 = 2 ^ d - 1 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (pred_pow_le d hd) (by decide))
  have h2 : (2 ^ d - 1) * (b.toNat * 2 ^ 144) % 2 ^ 256 = (2 ^ d - 1) * (b.toNat * 2 ^ 144) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
      (Nat.mul_le_mul (pred_pow_le d hd) (Nat.mul_le_mul_right _ (toNat_le_pred b)))
      (by decide))
  have e : (2 ^ d - 1) * (b.toNat * 2 ^ 144) + (a.toNat + b.toNat * 2 ^ 144) =
      a.toNat + ((2 ^ d - 1) * (b.toNat * 2 ^ 144) + b.toNat * 2 ^ 144) := by ac_rfl
  rw [h1, h2, e, scale_nat _ _ (Nat.two_pow_pos d), Nat.mul_comm (2 ^ d)]
  apply Nat.mod_eq_of_lt
  calc a.toNat + b.toNat * 2 ^ 144 * 2 ^ d
      ≤ (2 ^ 32 - 1) + (2 ^ 32 - 1) * 2 ^ 144 * 2 ^ 31 :=
        Nat.add_le_add (toNat_le_pred a)
          (Nat.mul_le_mul (Nat.mul_le_mul_right _ (toNat_le_pred b)) (pow_le_of_le_31 d hd))
    _ < 2 ^ 256 := by decide


private theorem scaled_toNat (a b : BitVec 32) (u v : Nat) :
    (Paired144LegacyProduct.scaled a b u v).toNat =
      (a.toNat * 2 ^ u + b.toNat * 2 ^ (144 + v)) % 2 ^ 256 := by
  simp only [Paired144LegacyProduct.scaled, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.add_mod_mod, Nat.mod_add_mod,
    Nat.mod_mul_mod]

theorem scaleLow_eq_scaled (a b : BitVec 32) (d : Nat) (hd : d ≤ 31) :
    scaleLow (pack a b) d = Paired144LegacyProduct.scaled a b d 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [scaled_toNat, Nat.add_zero]
  have h := scaleLow_toNat a b d hd
  rw [← h, Nat.mod_eq_of_lt (scaleLow (pack a b) d).isLt]

theorem scaleHigh_eq_scaled (a b : BitVec 32) (d : Nat) (hd : d ≤ 31) :
    scaleHigh (pack a b) d = Paired144LegacyProduct.scaled a b 0 d := by
  apply BitVec.eq_of_toNat_eq
  rw [scaled_toNat, Nat.pow_zero, Nat.mul_one, Nat.pow_add, ← Nat.mul_assoc]
  have h := scaleHigh_toNat a b d hd
  rw [← h, Nat.mod_eq_of_lt (scaleHigh (pack a b) d).isLt]

theorem bits_wordScale_lower (a b : BitVec 32) (d : Nat) (hd : d ≤ 31) :
    bits (wordScale (word (pack a b)) lowerWord d) = Paired144LegacyProduct.scaled a b d 0 := by
  rw [← scaleLow_eq_scaled a b d hd]
  simp only [wordScale, scaleLow, bits_add, bits_mul, bits_land, bits_ofNat,
    lowerWord, lowerMask, bits_word]

theorem bits_wordScale_upper (a b : BitVec 32) (d : Nat) (hd : d ≤ 31) :
    bits (wordScale (word (pack a b)) upperWord d) = Paired144LegacyProduct.scaled a b 0 d := by
  rw [← scaleHigh_eq_scaled a b d hd]
  simp only [wordScale, scaleHigh, bits_add, bits_mul, bits_land, bits_ofNat,
    upperWord, upperMask, bits_word]
#print axioms bits_wordScale_lower
#print axioms bits_wordScale_upper
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordScale
