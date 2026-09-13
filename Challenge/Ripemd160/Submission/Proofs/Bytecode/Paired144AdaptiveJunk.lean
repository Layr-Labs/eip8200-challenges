import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144AdaptiveInput
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144AdaptiveProduct
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRound

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144AdaptiveJunk
open Paired144Core Paired144AdaptiveInput

def wideH {w : Nat} (a : BitVec w) (b : BitVec 112) : BitVec 256 :=
  b ++ a.setWidth 144

theorem compact_wideH {w : Nat} (a : BitVec w) (b : BitVec 112) (g : Nat)
    (hg : g = 68 ∨ g = 69 ∨ g = 87)
    (hw : 32 ≤ w ∧ w ≤ g ∧ w ≤ 144 - g) :
    compact g (wideH a b) = small g (a.setWidth 32) (b.setWidth 32) := by
  have hg0 : 68 ≤ g ∧ g ≤ 87 := by rcases hg with h | h | h <;> omega
  have hm : BitVec.ofNat 256 ((2 ^ 32 - 1) * (1 + 2 ^ g)) =
      small g (BitVec.allOnes 32) (BitVec.allOnes 32) := by
    rcases hg with rfl | rfl | rfl <;> decide
  unfold compact
  rw [hm]
  unfold wideH small
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
        have ht : i - g < 256 - g := by omega
        have hb32 : i - g < 32 := by omega
        have he : 144 - g + i - 144 = i - g := by omega
        have hz := BitVec.getLsbD_of_ge a i (by omega)
        have hb112 : i - g < 112 := by omega
        simp [h32, hig, hi144, hs144, ht, hb32, he, hz, hb112]
      · have hb32 : ¬ i - g < 32 := by omega
        simp [h32, hig, hb32]

theorem wideH_toNat {w : Nat} (a : BitVec w) (b : BitVec 112) (hw : w ≤ 144) :
    (wideH a b).toNat = a.toNat + b.toNat * 2 ^ 144 := by
  unfold wideH
  rw [BitVec.toNat_append, BitVec.toNat_setWidth_of_le hw]
  have ha : a.toNat < 2 ^ 144 :=
    Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) hw)
  rw [← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

theorem wideH_ofNat (w A B : Nat) (hw : w ≤ 144)
    (hA : A < 2 ^ w) (hB : B < 2 ^ 112) :
    wideH (BitVec.ofNat w A) (BitVec.ofNat 112 B) = BitVec.ofNat 256 (A + B * 2 ^ 144) := by
  apply BitVec.eq_of_toNat_eq
  rw [wideH_toNat _ _ hw, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (StaggerRound.split_lt A B
    (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) hw)) hB)).symm

theorem compact_nat (w g A B : Nat) (hg : g = 68 ∨ g = 69 ∨ g = 87)
    (hw : 32 ≤ w ∧ w ≤ g ∧ w ≤ 144 - g)
    (hA : A < 2 ^ w) (hB : B < 2 ^ 112) :
    compact g (BitVec.ofNat 256 (A + B * 2 ^ 144)) =
      BitVec.ofNat 256 (A % 2 ^ 32) + (BitVec.ofNat 256 (B % 2 ^ 32) <<< g) := by
  have hw144 : w ≤ 144 := by omega
  rw [← wideH_ofNat w A B hw144 hA hB, compact_wideH _ _ g hg hw]
  rw [small_value _ _ g hg]
  simp only [BitVec.setWidth_ofNat_of_le hw.1,
    BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 112), BitVec.toNat_ofNat]

theorem compact_junk (A B jl jr g : Nat)
    (hA : A < 2 ^ 34) (hB : B < 2 ^ 34) (hjr : jr < 2 ^ 64)
    (hg : (g = 68 ∨ g = 69) ∧ jl < 2 ^ 32 ∨ g = 87 ∧ jl < 2 ^ 23) :
    compact g (BitVec.ofNat 256 (A + B * 2 ^ 144) + StaggerRound.junk jl jr) =
      BitVec.ofNat 256 (A % 2 ^ 32) + (BitVec.ofNat 256 (B % 2 ^ 32) <<< g) := by
  rw [StaggerRound.ofNat_add_junk]
  have hB' : B + jr * 2 ^ 32 < 2 ^ 112 := by
    simp only [Nat.reducePow] at *
    omega
  rcases hg with ⟨hg, hjl⟩ | ⟨rfl, hjl⟩
  · have hA' : A + jl * 2 ^ 32 < 2 ^ 65 := by
      simp only [Nat.reducePow] at *
      omega
    have hg' : g = 68 ∨ g = 69 ∨ g = 87 := by rcases hg with h | h <;> simp [h]
    have hw : 32 ≤ 65 ∧ 65 ≤ g ∧ 65 ≤ 144 - g := by
      rcases hg with rfl | rfl <;> decide
    rw [compact_nat 65 g _ _ hg' hw hA' hB']
    simp only [Nat.add_mul_mod_self_right]
  · -- gap 87 shifts bit 57 of the lower half onto bit 0: dead bits must stay below bit 57.
    have hA' : A + jl * 2 ^ 32 < 2 ^ 57 := by
      simp only [Nat.reducePow] at *
      omega
    rw [compact_nat 57 87 _ _ (by simp) (by decide) hA' hB']
    simp only [Nat.add_mul_mod_self_right]

#print axioms compact_wideH
#print axioms compact_junk
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144AdaptiveJunk
