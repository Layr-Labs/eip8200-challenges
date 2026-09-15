import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInput
import Mathlib.FieldTheory.Finite.Basic

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FermatMath

open EvmSemantics EvmSemantics.EVM WindowTwentyOneInput

theorem modPow_prime (p a : Nat) (hp : p.Prime) :
    Precompile.modPow a (p - 1) p = if a % p = 0 then 0 else 1 := by
  rw [Algorithm.modPow_eq, if_neg hp.ne_zero]
  by_cases h : a % p = 0
  · rw [if_pos h, Nat.pow_mod, h, zero_pow (by have := hp.two_le; omega), Nat.zero_mod]
  · rw [if_neg h]
    have hc : a.Coprime p := (hp.coprime_iff_not_dvd.mpr (by
      simpa only [Nat.dvd_iff_mod_eq_zero] using h)).symm
    have hf := Nat.ModEq.pow_card_sub_one_eq_one hp hc
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using hf

theorem baseWord_toNat_all (input : ByteArray) (hwidth : baseSize input ≤ 32) :
    (baseWord input).toNat = baseValue input := by
  by_cases hp : 0 < baseSize input
  · exact baseWord_toNat input hp hwidth
  · have hz : baseSize input = 0 := by omega
    simp [baseWord, baseValue, hz, UInt256.shiftRight,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width]
    rfl

private theorem mod_toNat (a b : UInt256) (hb : b.toNat ≠ 0) :
    (UInt256.mod a b).toNat = a.toNat % b.toNat := by
  change (if b.toNat = 0 then (0 : UInt256) else UInt256.mk (a.val % b.val)).toNat = _
  rw [if_neg hb]
  exact Fin.mod_val a.val b.val

/-- Fermat's result is zero exactly when the base is divisible by the prime. -/
def resultWord (input : ByteArray) : UInt256 :=
  UInt256.isZero (UInt256.isZero (UInt256.mod (baseWord input) (modulusWord input)))

theorem resultWord_toNat (input : ByteArray) (hwidth : baseSize input ≤ 32)
    (hm : modulusValue input ≠ 0) :
    (resultWord input).toNat = if baseValue input % modulusValue input = 0 then 0 else 1 := by
  have hw : (modulusWord input).toNat ≠ 0 := by rwa [modulusWord_toNat]
  simp only [resultWord, Challenge.EvmProof.Word.word_toNat_isZero, mod_toNat _ _ hw,
    baseWord_toNat_all input hwidth, modulusWord_toNat]
  split <;> simp_all

theorem result_spec (input : ByteArray) (hmatch : Matches input)
    (hp : (modulusValue input).Prime)
    (he : exponentValue input = modulusValue input - 1) :
    spec input = Precompile.natToBytes (resultWord input).toNat 32 := by
  rw [spec_eq input hmatch, he, modPow_prime _ _ hp,
    resultWord_toNat input hmatch.1 hp.ne_zero]

end Challenge.Modexp.Submission.Proofs.Bytecode.FermatMath
