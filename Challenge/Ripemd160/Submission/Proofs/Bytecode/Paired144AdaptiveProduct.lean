import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Carry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Nat
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactGap

set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144AdaptiveProduct
open Paired144Core

def rawProduct (a b : BitVec 32) (g u v : Nat) : BitVec 256 :=
  (BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< g)) *
    Paired144CompactGap.coefficient u v

abbrev fixedProduct (a b : BitVec 32) (g : Nat) : BitVec 256 := rawProduct a b g 6 0

def Cases (g n r s : Nat) : Prop :=
  (g = 68 ∧ n = 23 ∧ r = 15 ∧ s = 5) ∨
  (g = 69 ∧ n = 23 ∧ r = 15 ∧ s = 6) ∨
  (g = 87 ∧ n = 32 ∧ r = 6 ∧ s = 15)

theorem rawProduct_nat (a b : BitVec 32) (g u v : Nat) :
    (rawProduct a b g u v).toNat =
      ((a.toNat + b.toNat * 2 ^ g) * ((2 ^ 32 + 1) * (2 ^ u + 2 ^ (72 + v)))) % 2 ^ 256 := by
  simp only [rawProduct, Paired144CompactGap.coefficient, BitVec.toNat_mul, BitVec.toNat_add,
    BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]

theorem rawProduct_low72 (a b : BitVec 32) (g : Nat)
    (hg : g = 68 ∨ g = 69 ∨ g = 87) :
    (fixedProduct a b g).toNat % 2 ^ 72 = a.toNat * (2 ^ 32 + 1) * 2 ^ 6 := by
  have ha := a.isLt
  have hb := b.isLt
  rw [fixedProduct, rawProduct_nat]
  rcases hg with rfl | rfl | rfl <;> simp only [Nat.reducePow] at * <;> omega

theorem rawProduct_div (a b : BitVec 32) (g : Nat)
    (hg : g = 68 ∨ g = 69 ∨ g = 87) :
    (fixedProduct a b g).toNat / 2 ^ (g + 72) = b.toNat * (2 ^ 32 + 1) := by
  have ha := a.isLt
  have hb := b.isLt
  rw [fixedProduct, rawProduct_nat]
  have hw : ((a.toNat + b.toNat * 2 ^ g) *
      ((2 ^ 32 + 1) * (2 ^ 6 + 2 ^ (72 + 0)))) < 2 ^ 256 := by
    rcases hg with rfl | rfl | rfl <;> simp only [Nat.reducePow, Nat.reduceAdd] at * <;> omega
  rw [Nat.mod_eq_of_lt hw]
  rcases hg with rfl | rfl | rfl <;> simp only [Nat.reducePow, Nat.reduceAdd] at * <;> omega

theorem shifted_gap (a b : BitVec 32) (g n : Nat)
    (hg : g = 68 ∨ g = 69 ∨ g = 87) (hn : n ≤ 71) :
    (fixedProduct a b g >>> n).getLsbD (71 - n) = false := by
  rw [BitVec.getLsbD_ushiftRight, show n + (71 - n) = 71 from by omega]
  rw [← BitVec.testBit_toNat]
  have hm := Nat.testBit_mod_two_pow (fixedProduct a b g).toNat 72 71
  simp only [show decide (71 < 72) = true from rfl, Bool.true_and] at hm
  rw [← hm, rawProduct_low72 a b g hg]
  apply Nat.testBit_lt_two_pow
  have ha := a.isLt
  simp only [Nat.reducePow] at *
  omega

theorem low_from_residue (x : BitVec 256) (a : BitVec 32) (n r : Nat)
    (hn : 6 ≤ n ∧ n + 32 ≤ 72) (hr : 0 < r ∧ r < 32)
    (he : n - 6 = 32 - r)
    (hx : x.toNat % 2 ^ 72 = a.toNat * (2 ^ 32 + 1) * 2 ^ 6) :
    low (x >>> n) = a.rotateLeft r := by
  apply BitVec.eq_of_toNat_eq
  simp only [low, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  rw [← Paired144Nat.truncate_window _ n 32 72 hn.2, hx,
    Paired144Nat.mul_pow_div_pow _ 6 n hn.1, he,
    Paired144Nat.rotate_toNat a r hr.1 hr.2]

theorem high_from_quotient (x : BitVec 256) (b : BitVec 32) (g n s : Nat)
    (hs : 0 < s ∧ s < 32)
    (hp : 2 ^ n * 2 ^ 144 = 2 ^ (g + 72) * 2 ^ (32 - s))
    (hx : x.toNat / 2 ^ (g + 72) = b.toNat * (2 ^ 32 + 1)) :
    high (x >>> n) = b.rotateLeft s := by
  apply BitVec.eq_of_toNat_eq
  simp only [high, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul, hp, ← Nat.div_div_eq_div_mul, hx,
    Paired144Nat.rotate_toNat b s hs.1 hs.2]

theorem low_shifted (a b : BitVec 32) (g n r s : Nat) (h : Cases g n r s) :
    low (fixedProduct a b g >>> n) = a.rotateLeft r := by
  have hg : g = 68 ∨ g = 69 ∨ g = 87 := by rcases h with h | h | h <;> simp_all
  have hn : 6 ≤ n ∧ n + 32 ≤ 72 := by rcases h with h | h | h <;> simp_all
  have hr : 0 < r ∧ r < 32 := by rcases h with h | h | h <;> simp_all
  have he : n - 6 = 32 - r := by rcases h with h | h | h <;> simp_all
  exact low_from_residue _ a n r hn hr he (rawProduct_low72 a b g hg)

theorem high_shifted (a b : BitVec 32) (g n r s : Nat) (h : Cases g n r s) :
    high (fixedProduct a b g >>> n) = b.rotateLeft s := by
  have hg : g = 68 ∨ g = 69 ∨ g = 87 := by rcases h with h | h | h <;> simp_all
  have hs : 0 < s ∧ s < 32 := by rcases h with h | h | h <;> simp_all
  have hp : 2 ^ n * 2 ^ 144 = 2 ^ (g + 72) * 2 ^ (32 - s) := by
    rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide
  exact high_from_quotient _ b g n s hs hp (rawProduct_div a b g hg)

theorem normalize_shifted_add (a b e f : BitVec 32) (g n r s : Nat)
    (h : Cases g n r s) :
    normalize ((fixedProduct a b g >>> n) + pack e f) =
      pack (a.rotateLeft r + e) (b.rotateLeft s + f) := by
  have hg : g = 68 ∨ g = 69 ∨ g = 87 := by rcases h with h | h | h <;> simp_all
  have hn : 23 ≤ n ∧ n ≤ 32 := by rcases h with h | h | h <;> simp_all
  rw [Paired144Carry.normalize_add_pack _ e f (71 - n) (by omega) (by omega)
    (shifted_gap a b g n hg (by omega)), low_shifted a b g n r s h,
    high_shifted a b g n r s h]

#print axioms rawProduct_low72
#print axioms low_shifted
#print axioms high_shifted
#print axioms normalize_shifted_add
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144AdaptiveProduct
