import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Core

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Carry

open Paired144Core

/-- A zero bit below a power-of-two boundary leaves room for a smaller
addend, regardless of all other bits. -/
theorem add_no_carry_nat (x e k w : Nat) (hk : k < w)
    (hx : x < 2 ^ w) (he : e < 2 ^ k) (hbit : x / 2 ^ k % 2 = 0) :
    x + e < 2 ^ w := by
  let q := 2 ^ (k + 1)
  have hq : q = 2 ^ k * 2 := Nat.pow_succ ..
  have hdiv : q ∣ 2 ^ w := Nat.pow_dvd_pow 2 (by omega)
  have hrem : x % q < 2 ^ k := by
    rw [hq, Nat.mod_mul, hbit, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_lt _ (Nat.two_pow_pos k)
  have hroom : x % q + e < q := by
    have hsum : x % q + e < 2 ^ k * 2 := by omega
    simpa only [← hq] using hsum
  have hquot : x / q < 2 ^ w / q := Nat.div_lt_div_of_lt_of_dvd hdiv hx
  calc
    x + e = x / q * q + (x % q + e) := by
      have h := Nat.div_add_mod' x q
      omega
    _ < x / q * q + q := Nat.add_lt_add_left hroom _
    _ = (x / q + 1) * q := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ (2 ^ w / q) * q := Nat.mul_le_mul_right q (by omega)
    _ = 2 ^ w := Nat.div_mul_cancel hdiv

theorem add32_no_carry144 (x : BitVec 144) (e : BitVec 32) (k : Nat)
    (hk32 : 32 ≤ k) (hk144 : k < 144) (hgap : x.getLsbD k = false) :
    x.toNat + e.toNat < 2 ^ 144 := by
  have hbit : x.toNat / 2 ^ k % 2 = 0 := by
    have hnot : ¬ x.toNat / 2 ^ k % 2 = 1 := by
      simpa only [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
        decide_eq_false_iff_not] using hgap
    have hmod := Nat.mod_lt (x.toNat / 2 ^ k) (by decide : 0 < 2)
    omega
  have he : e.toNat < 2 ^ k :=
    Nat.lt_of_lt_of_le e.isLt (Nat.pow_le_pow_right (by decide) hk32)
  exact add_no_carry_nat x.toNat e.toNat k 144 hk144 x.isLt he hbit

theorem high_add_nat (n e f : Nat)
    (hcarry : n % 2 ^ 144 + e < 2 ^ 144) :
    (((n + (e + 2 ^ 144 * f)) % 2 ^ 256) / 2 ^ 144) % 2 ^ 32 =
      (n / 2 ^ 144 % 2 ^ 32 + f) % 2 ^ 32 := by
  simp only [Nat.reducePow] at *
  omega

/-- Both the compact and legacy rotations can provide their own spacer
position; no fixed bit from an earlier packed representation is assumed. -/
theorem normalize_add_pack (x : BitVec 256) (e f : BitVec 32) (k : Nat)
    (hk32 : 32 ≤ k) (hk144 : k < 144) (hgap : x.getLsbD k = false) :
    normalize (x + pack e f) = pack (low x + e) (high x + f) := by
  have hgap' : (x.extractLsb' 0 144).getLsbD k = false := by
    simpa only [BitVec.getLsbD_extractLsb', Nat.zero_add,
      show decide (k < 144) = true from decide_eq_true hk144, Bool.true_and] using hgap
  have hcarry := add32_no_carry144 (x.extractLsb' 0 144) e k hk32 hk144 hgap'
  have hcarryNat : x.toNat % 2 ^ 144 + e.toNat < 2 ^ 144 := by
    simpa only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] using hcarry
  have hp : (pack e f).toNat = e.toNat + 2 ^ 144 * f.toNat := by
    rw [pack_toNat, Nat.mul_comm f.toNat]
  have hlo : low (x + pack e f) = low x + e := by
    change (x + pack e f).extractLsb' 0 32 = low x + e
    rw [BitVec.extractLsb'_add (by decide)]
    exact congrArg (fun y => low x + y) (low_pack e f)
  have hhi : high (x + pack e f) = high x + f := by
    apply BitVec.eq_of_toNat_eq
    simp only [high, BitVec.extractLsb'_toNat, BitVec.toNat_add, hp,
      Nat.shiftRight_eq_div_pow]
    exact high_add_nat x.toNat e.toNat f.toNat hcarryNat
  exact congr (congrArg pack hlo) hhi

#print axioms add_no_carry_nat
#print axioms add32_no_carry144
#print axioms high_add_nat
#print axioms normalize_add_pack

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Carry
