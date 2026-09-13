import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactInput

set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144AdaptiveInput
open Paired144Core

def compact (g : Nat) (x : BitVec 256) : BitVec 256 :=
  (x ||| (x >>> (144 - g))) &&& BitVec.ofNat 256 ((2 ^ 32 - 1) * (1 + 2 ^ g))

def wide (a b : BitVec 34) : BitVec 256 := b.setWidth 112 ++ a.setWidth 144
def small (g : Nat) (a b : BitVec 32) : BitVec 256 :=
  (b.setWidth (256 - g) ++ a.setWidth g).setWidth 256

theorem compact_wide (a b : BitVec 34) (g : Nat)
    (hg : g = 68 ∨ g = 69 ∨ g = 87) :
    compact g (wide a b) = small g (a.setWidth 32) (b.setWidth 32) := by
  have hg0 : 68 ≤ g ∧ g ≤ 87 := by rcases hg with h | h | h <;> omega
  have hm : BitVec.ofNat 256 ((2 ^ 32 - 1) * (1 + 2 ^ g)) =
      small g (BitVec.allOnes 32) (BitVec.allOnes 32) := by
    rcases hg with rfl | rfl | rfl <;> decide
  unfold compact
  rw [hm]
  unfold wide small
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    hi, decide_true, Bool.true_and]
  by_cases h32 : i < 32
  · have hig : i < g := by omega
    have hi144 : i < 144 := by omega
    have hs144 : 144 - g + i < 144 := by omega
    have hz := BitVec.getLsbD_of_ge a (144 - g + i) (by omega)
    simp [h32, hig, hi144, hs144, hz]
  · by_cases hig : i < g
    · simp [h32, hig]
    · by_cases htop : i < g + 32
      · have hi144 : i < 144 := by omega
        have hs144 : ¬144 - g + i < 144 := by omega
        have hb112 : 144 - g + i - 144 < 112 := by omega
        have ht : i - g < 256 - g := by omega
        have hb32 : i - g < 32 := by omega
        have he : 144 - g + i - 144 = i - g := by omega
        have hz := BitVec.getLsbD_of_ge a i (by omega)
        have hb112a : i - g < 112 := by omega
        simp [h32, hig, hi144, hs144, hb112, hb112a, ht, hb32, he, hz]
      · have hb32 : ¬ i - g < 32 := by omega
        simp [h32, hig, hb32]

theorem small_value (a b : BitVec 32) (g : Nat)
    (hg : g = 68 ∨ g = 69 ∨ g = 87) :
    small g a b = BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< g) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  rcases hg with rfl | rfl | rfl
  all_goals
    simp only [small, Nat.reduceSub, Nat.reduceAdd, BitVec.setWidth_eq]
    rw [BitVec.toNat_append, BitVec.toNat_setWidth_of_le (by decide),
      BitVec.toNat_setWidth_of_le (by decide)]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (show a.toNat < 2 ^ _ from by
      simp only [Nat.reducePow] at *; omega), Nat.shiftLeft_eq, Nat.add_comm]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod]
    apply (Nat.mod_eq_of_lt _).symm
    simp only [Nat.reducePow] at *
    omega

theorem wide_toNat (a b : BitVec 34) :
    (wide a b).toNat = a.toNat + b.toNat * 2^144 := by
  unfold wide
  rw [BitVec.toNat_append, BitVec.toNat_setWidth_of_le (by decide),
    BitVec.toNat_setWidth_of_le (by decide)]
  have ha : a.toNat < 2^144 := by have := a.isLt; simp only [Nat.reducePow] at *; omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

theorem wide_ofNat (a b : Nat) (ha : a<2^34) (hb : b<2^34) :
    wide (BitVec.ofNat 34 a) (BitVec.ofNat 34 b) =
      BitVec.ofNat 256 (a+b*2^144) := by
  apply BitVec.eq_of_toNat_eq
  rw [wide_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, BitVec.toNat_ofNat]
  apply (Nat.mod_eq_of_lt _).symm
  simp only [Nat.reducePow] at *; omega

theorem four_adds_wide (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32) :
    (((pack a0 b0+pack a1 b1)+pack a2 b2)+pack a3 b3) =
      wide (BitVec.ofNat 34 (a0.toNat+a1.toNat+a2.toNat+a3.toNat))
        (BitVec.ofNat 34 (b0.toNat+b1.toNat+b2.toNat+b3.toNat)) := by
  rw [wide_ofNat]
  · rw [pack_eq_ofNat,pack_eq_ofNat,pack_eq_ofNat,pack_eq_ofNat]
    simp only [BitVec.ofNat_add_ofNat, Nat.add_mul]
    congr 1; omega
  · have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
    simp only [Nat.reducePow] at *; omega
  · have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
    simp only [Nat.reducePow] at *; omega

theorem compact_four_adds (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32) (g : Nat)
    (hg : g = 68 ∨ g = 69 ∨ g = 87) :
    compact g (((pack a0 b0 + pack a1 b1) + pack a2 b2) + pack a3 b3) =
      BitVec.ofNat 256 ((((a0 + a1) + a2) + a3).toNat) +
        (BitVec.ofNat 256 ((((b0 + b1) + b2) + b3).toNat) <<< g) := by
  rw [← small_value _ _ g hg, four_adds_wide, compact_wide _ _ g hg]
  simp only [BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 34)]
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

#print axioms compact_four_adds

#print axioms compact_wide
#print axioms small_value
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144AdaptiveInput
