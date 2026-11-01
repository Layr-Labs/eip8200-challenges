import Challenge.Modexp.Submission.Proofs.Cycle.WordArithmetic
import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq
import Challenge.EvmProof.Word
set_option warningAsError true
namespace CycleSubmission.DirectRecovery

/-- The consumer asks for a radix carry, not the complete CRT reconstruction. -/
theorem direct_carry (H P beta factor carry digit : ℕ)
    (hfit : digit ≤ H + P) (hc : carry < P)
    (hresidue : H ≡ beta * carry + digit [MOD P])
    (hinverse : beta * factor = P + 1) :
    ((H + P - digit) * factor) % P = carry := by
  have hadd : H + P - digit + digit ≡ beta * carry + digit [MOD P] := by
    rw [Nat.sub_add_cancel hfit]
    simpa [Nat.ModEq, Nat.add_mod] using hresidue
  have hsub := hadd.add_right_cancel' digit
  have hmul := hsub.mul_right factor
  have heq : beta * carry * factor = carry * (P + 1) := by
    rw [← hinverse]
    ring
  rw [heq] at hmul
  simpa [Nat.ModEq, Nat.mul_add, Nat.add_mod, Nat.mod_eq_of_lt hc] using hmul

/-- A sufficient, deliberately loose bound for an 18-product column. -/
theorem column_bound (beta P carry products : ℕ)
    (hc : carry < P) (hproducts : products ≤ 18 * (beta - 1)^2)
    (hroom : P + 18 * (beta - 1)^2 ≤ beta * P) :
    carry + products < beta * P := by omega

theorem r9_room : (2^251-1) + 18*(2^244-1)^2 ≤ 2^244*(2^251-1) := by norm_num
theorem r5_room : (2^251-1) + 18*(2^240-1)^2 ≤ 2^240*(2^251-1) := by norm_num
theorem r9_inverse : (2^244:ℕ)*128 = (2^251-1)+1 := by norm_num
theorem r5_inverse : (2^240:ℕ)*2048 = (2^251-1)+1 := by norm_num

theorem carry_lt (T beta P : ℕ) (hbeta : 0 < beta) (hT : T < beta * P) :
    T / beta < P := by
  apply (Nat.div_lt_iff_lt_mul hbeta).2
  simpa [Nat.mul_comm] using hT

/-- Biasing by P makes the digit subtraction exact even when H < digit. -/
theorem biased_word_sub (H P digit B : ℕ)
    (hB : 0 < B) (hH : H < B) (hd : digit < B)
    (hfit : digit ≤ H + P) (hresult : H + P - digit < B) :
    (((H + B - digit) % B) + P) % B = H + P - digit := by
  by_cases h : digit ≤ H
  · have he : H + B - digit = (H - digit) + B := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : H-digit<B)]
    have he' : H - digit + P = H + P - digit := by omega
    rw [he', Nat.mod_eq_of_lt hresult]
  · have hsmall : H + B - digit < B := by omega
    rw [Nat.mod_eq_of_lt hsmall]
    have he : H + B - digit + P = (H + P - digit) + B := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hresult]

theorem residue_bias_bounds (H digit beta : ℕ)
    (hH : H < 19 * (2^251-1)) (hd : digit < beta) (hb : beta ≤ 2^244) :
    digit ≤ H + (2^251-1) ∧ H + (2^251-1) - digit < 2^256 := by
  constructor <;> omega

theorem low_digit (T B beta : ℕ) (h : beta ∣ B) :
    (T % B) % beta = T % beta := Nat.mod_mod_of_dvd T h

theorem column_recovery (T H beta factor : ℕ)
    (hbeta : 0 < beta) (hb : beta ≤ 2^244) (hdiv : beta ∣ 2^256)
    (hT : T < beta * (2^251-1)) (hH : H < 19*(2^251-1))
    (hresidue : H ≡ T [MOD (2^251-1)])
    (hinverse : beta * factor = (2^251-1)+1) :
    ((H + (2^251-1) - ((T % 2^256) % beta)) * factor) % (2^251-1) = T / beta := by
  rw [low_digit T _ _ hdiv]
  apply direct_carry H (2^251-1) beta factor (T/beta) (T%beta)
  · exact (residue_bias_bounds H (T%beta) beta hH (Nat.mod_lt T hbeta) hb).1
  · exact carry_lt T beta _ hbeta hT
  · simpa only [Nat.div_add_mod] using hresidue
  · exact hinverse

/-- The actual wrapping word expression used by the changed EVM slices. -/
theorem word_direct_carry (H digit p factor : EvmSemantics.UInt256) (beta carry : ℕ)
    (hp : 0 < p.toNat) (hfit : digit.toNat ≤ H.toNat + p.toNat)
    (hresult : H.toNat + p.toNat - digit.toNat < 2^256)
    (hc : carry < p.toNat)
    (hresidue : H.toNat ≡ beta * carry + digit.toNat [MOD p.toNat])
    (hinverse : beta * factor.toNat = p.toNat + 1) :
    (EvmSemantics.UInt256.mulMod (p + (H - digit)) factor p).toNat = carry := by
  have hbias : (p + (H - digit)).toNat = H.toNat + p.toNat - digit.toNat := by
    rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_sub]
    rw [Nat.add_comm p.toNat, Nat.add_comm (2^256) H.toNat]
    exact biased_word_sub _ _ _ _ (by norm_num) H.val.isLt digit.val.isLt hfit hresult
  have hne : p.val.val ≠ 0 := Nat.ne_of_gt hp
  rw [EvmSemantics.UInt256.mulMod, if_neg hne, Challenge.EvmProof.Word.word_toNat_ofNat]
  change ((p + (H - digit)).toNat * factor.toNat % p.toNat) % 2^256 = carry
  rw [hbias, direct_carry _ _ _ _ _ _ hfit hc hresidue hinverse]
  exact Nat.mod_eq_of_lt (lt_trans hc p.val.isLt)

#print axioms direct_carry
#print axioms column_bound
#print axioms r9_room
#print axioms r5_room
#print axioms r9_inverse
#print axioms r5_inverse
#print axioms carry_lt
#print axioms biased_word_sub
#print axioms residue_bias_bounds
#print axioms low_digit
#print axioms column_recovery
#print axioms word_direct_carry
open EvmSemantics
open Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.ColumnExpressions
open HistoricalSearch.WordCancellation
open CycleSubmission.WordArithmetic
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def carry (H lo : UInt256) : UInt256 :=
  UInt256.mulMod (P + (H - UInt256.land (UInt256.ofNat (2^240-1)) lo))
    (UInt256.ofNat 2048) P

theorem expression_contract (hi lo : Expr) (C : Nat)
    (hcount : hi.count ≤ 19) (hlit : hi.literalsBounded (residueModulus-1))
    (hvalue : hi.value = lo.value)
    (hC : C ≤ 18*(radix-1)) (hS : hi.value ≤ 18*(radix-1)^2+C) :
    (carry (hi.high P) lo.low).toNat = hi.value / radix := by
  have hh := highInvariant P pValue hi hcount hlit
  have hH : (hi.high P).toNat < 19*(2^251-1) := by
    have hm := Nat.mul_le_mul_right (residueModulus-1) hcount
    norm_num [residueModulus] at hm hh ⊢
    omega
  have hd : (UInt256.land (UInt256.ofNat (2^240-1)) lo.low).toNat = hi.value % radix := by
    rw [land_comm]
    change (lo.low &&& UInt256.ofNat (2^240-1)).toNat = hi.value % radix
    rw [mask_toNat _ 240 (by decide), lowValue, ← hvalue]
    exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 240 ≤ 256))
  have hb := residue_bias_bounds (hi.high P).toNat (hi.value%radix) radix
    hH (Nat.mod_lt _ (Nat.two_pow_pos _)) (by norm_num [radix])
  have hc := (CycleSubmission.Bounds.fullColumnBounds hi.value C hC hS).2.1
  unfold carry
  apply word_direct_carry _ _ _ _ radix (hi.value/radix)
  · rw [pValue]; norm_num [residueModulus]
  · rw [pValue, hd]; exact hb.1
  · rw [pValue, hd]; exact hb.2
  · rw [pValue]; exact hc
  · rw [pValue, hd, Nat.div_add_mod]; exact hh.2
  · norm_num [radix, word_toNat_ofNat, pValue, residueModulus]

#print axioms expression_contract
end CycleSubmission.DirectRecovery
