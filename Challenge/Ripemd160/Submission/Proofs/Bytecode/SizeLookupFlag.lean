import Challenge.EvmProof.Word
import Mathlib.Data.Nat.Bitwise

set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
open EvmSemantics
open Challenge.EvmProof

def maskNat : Nat := (2 ^ 56 ||| 2 ^ 120) ||| 2 ^ 63
def mask : UInt256 := UInt256.ofNat maskNat

theorem mask_literal : mask = UInt256.ofNat 1329227995784915882199236691173048320 := by decide
private theorem mask_toNat : mask.toNat = maskNat := by decide

private theorem mask_bit_false (n : Nat) (h56 : n ≠ 56) (h120 : n ≠ 120)
    (h128 : n ≠ 63) : maskNat.testBit n = false := by
  simp only [maskNat, Nat.testBit_or,
    Nat.testBit_two_pow_of_ne (Ne.symm h56),
    Nat.testBit_two_pow_of_ne (Ne.symm h120),
    Nat.testBit_two_pow_of_ne (Ne.symm h128), Bool.false_or]

private theorem bit_zero (x : UInt256) (h56 : x.toNat ≠ 56)
    (h120 : x.toNat ≠ 120) (h128 : x.toNat ≠ 63) :
    UInt256.land (UInt256.ofNat 1) (UInt256.shiftRight mask x) = UInt256.ofNat 0 := by
  by_cases hbig : x.toNat ≥ 256
  · simp only [UInt256.shiftRight, if_pos hbig]
    decide
  · have hsmall : x.toNat < 256 := by omega
    have hsr := Word.shiftRight_toNat mask hsmall
    rw [← Word.word_eq_ofNat_toNat x] at hsr
    apply Word.word_ext
    rw [Word.word_toNat_land, hsr, mask_toNat]
    change 1 &&& (maskNat >>> x.toNat) = 0
    have hb : (maskNat >>> x.toNat).testBit 0 = false := by
      rw [Nat.testBit_shiftRight]
      simpa only [Nat.add_zero] using mask_bit_false x.toNat h56 h120 h128
    have h := Nat.two_pow_and (maskNat >>> x.toNat) 0
    simpa [hb] using h

private theorem eq_zero (n : Nat) (hn : n < 2 ^ 256) (x : UInt256)
    (hx : x.toNat ≠ n) : UInt256.eq (UInt256.ofNat n) x = UInt256.ofNat 0 := by
  unfold UInt256.eq
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hn, if_neg (Ne.symm hx)]

theorem flag (x : UInt256) :
    UInt256.isZero (UInt256.land (UInt256.ofNat 1) (UInt256.shiftRight mask x)) =
      UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.ofNat 63) x)
        (UInt256.lor (UInt256.eq (UInt256.ofNat 120) x) (UInt256.eq (UInt256.ofNat 56) x))) := by
  by_cases h56 : x = UInt256.ofNat 56
  · subst x; decide
  by_cases h120 : x = UInt256.ofNat 120
  · subst x; decide
  by_cases h128 : x = UInt256.ofNat 63
  · subst x; decide
  have n56 : x.toNat ≠ 56 := by
    intro h
    apply h56
    apply Word.word_ext
    change x.toNat = 56
    exact h
  have n120 : x.toNat ≠ 120 := by
    intro h
    apply h120
    apply Word.word_ext
    change x.toNat = 120
    exact h
  have n128 : x.toNat ≠ 63 := by
    intro h
    apply h128
    apply Word.word_ext
    change x.toNat = 63
    exact h
  rw [bit_zero x n56 n120 n128,
    eq_zero 56 (by decide) x n56, eq_zero 120 (by decide) x n120,
    eq_zero 63 (by decide) x n128]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
