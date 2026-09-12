import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactRotation
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactInput
open Paired144Core Paired144CompactGap

def compact (x : BitVec 256) : BitVec 256 :=
  (x ||| (x >>> 72)) &&& BitVec.ofNat 256 ((2^32-1)*(1+2^72))
def wide (a b : BitVec 72) : BitVec 256 := b.setWidth 112 ++ a.setWidth 144
def small (a b : BitVec 32) : BitVec 256 := b.setWidth 184 ++ a.setWidth 72

theorem compact_wide (a b : BitVec 72) :
    compact (wide a b) = small (a.setWidth 32) (b.setWidth 32) := by
  have hmask : BitVec.ofNat 256 ((2^32-1)*(1+2^72)) =
      small (BitVec.allOnes 32) (BitVec.allOnes 32) := by decide
  unfold compact
  rw [hmask]
  unfold wide small
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    Nat.add_comm 72 i, BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  by_cases h32 : i < 32
  · have h72 : i < 72 := by omega
    have h144 : i < 144 := by omega
    have hsum : i+72 <144 := by omega
    have hsum256 : i+72 <256 := by omega
    have hz := BitVec.getLsbD_of_ge a (i+72) (show 72 ≤ i+72 by omega)
    simp only [Bool.or_false, ite_false, h32,h72,h144,hsum,hsum256,if_pos,decide_true, Bool.true_and, Bool.and_true, hz, Bool.or_false]
  · by_cases h72 : i < 72
    · simp only [ite_false, h72,h32,if_pos,decide_false,Bool.false_and,Bool.and_false,ite_false]
    · by_cases h104 : i <104
      · have h144 : i<144 := by omega
        have hsum : ¬i+72<144 := by omega
        have hs112 : i+72-144<112 := by omega
        have hs32 : i-72<32 := by omega
        have h112 : i-72<112 := by omega
        have hs184 : i-72<184 := by omega
        have hs256 : i+72<256 := by omega
        have heq : i+72-144=i-72 := by omega
        have hz := BitVec.getLsbD_of_ge a i (show 72 ≤ i by omega)
        simp only [ite_false, h72,h144,hsum,hs112,h112,hs32,hs184,hs256,heq,if_pos,if_neg,
          decide_true,Bool.true_and,Bool.and_true,hz,Bool.false_or]
      · have hs32 : ¬i-72<32 := by omega
        simp only [ite_false, h72,hs32,if_neg,decide_false,Bool.false_and,Bool.and_false,ite_false]

theorem wide_toNat (a b : BitVec 72) :
    (wide a b).toNat = a.toNat + b.toNat * 2^144 := by
  unfold wide
  rw [BitVec.toNat_append, BitVec.toNat_setWidth_of_le (by decide),
    BitVec.toNat_setWidth_of_le (by decide)]
  have ha : a.toNat < 2^144 := by have := a.isLt; simp only [Nat.reducePow] at *; omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

theorem wide_ofNat (a b : Nat) (ha : a<2^72) (hb : b<2^72) :
    wide (BitVec.ofNat 72 a) (BitVec.ofNat 72 b) =
      BitVec.ofNat 256 (a+b*2^144) := by
  apply BitVec.eq_of_toNat_eq
  rw [wide_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, BitVec.toNat_ofNat]
  apply (Nat.mod_eq_of_lt _).symm
  simp only [Nat.reducePow] at *; omega

theorem small_value (a b : BitVec 32) :
    small a b = BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< 72) := by
  apply BitVec.eq_of_toNat_eq
  unfold small
  rw [BitVec.toNat_append, BitVec.toNat_setWidth_of_le (by decide),
    BitVec.toNat_setWidth_of_le (by decide)]
  have ha : a.toNat<2^72 := by have := a.isLt; simp only [Nat.reducePow] at *; omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod]
  apply (Nat.mod_eq_of_lt _).symm
  have ha := a.isLt; have hb := b.isLt
  simp only [Nat.reducePow] at *; omega

theorem four_adds_wide (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32) :
    (((pack a0 b0+pack a1 b1)+pack a2 b2)+pack a3 b3) =
      wide (BitVec.ofNat 72 (a0.toNat+a1.toNat+a2.toNat+a3.toNat))
        (BitVec.ofNat 72 (b0.toNat+b1.toNat+b2.toNat+b3.toNat)) := by
  rw [wide_ofNat]
  · rw [pack_eq_ofNat,pack_eq_ofNat,pack_eq_ofNat,pack_eq_ofNat]
    simp only [BitVec.ofNat_add_ofNat, Nat.add_mul]
    congr 1; omega
  · have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
    simp only [Nat.reducePow] at *; omega
  · have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
    simp only [Nat.reducePow] at *; omega

theorem compact_four_adds (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32) :
    compact (((pack a0 b0+pack a1 b1)+pack a2 b2)+pack a3 b3) =
      BitVec.ofNat 256 ((((a0+a1)+a2)+a3).toNat) +
        (BitVec.ofNat 256 ((((b0+b1)+b2)+b3).toNat) <<< 72) := by
  rw [← small_value, four_adds_wide, compact_wide]
  simp only [BitVec.setWidth_ofNat_of_le (by decide : 32≤72)]
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem normalize_four_adds (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32) :
    normalize (((pack a0 b0+pack a1 b1)+pack a2 b2)+pack a3 b3) =
      pack (((a0+a1)+a2)+a3) (((b0+b1)+b2)+b3) := by
  rw [four_adds_wide]
  unfold normalize low high wide
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide),
    BitVec.extractLsb'_append_eq_of_le (by decide)]
  simp only [Nat.sub_self]
  rw [BitVec.extractLsb'_setWidth_of_le (by decide),
    BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp only [← BitVec.setWidth_eq_extractLsb' (by decide : 32≤72),
    BitVec.setWidth_ofNat_of_le (by decide : 32≤72)]
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

#print axioms compact_wide
#print axioms compact_four_adds
#print axioms normalize_four_adds
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactInput
