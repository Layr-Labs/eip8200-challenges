import Challenge.EvmProof.Word
import Mathlib.Data.Nat.Bitwise
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
open EvmSemantics
open Challenge.EvmProof

/-- Exact size membership for the seven short checked scan paths. -/
def maskNat : Nat := (2 ^ 0) ||| (2 ^ 64) ||| (2 ^ 7) ||| (2 ^ 8) ||| (2 ^ 9) ||| (2 ^ 72) ||| (2 ^ 63)
def mask : UInt256 := UInt256.ofNat maskNat
theorem mask_literal : mask = UInt256.ofNat 4750036598980209542017 := by decide
private theorem mask_toNat : mask.toNat = maskNat := by decide

private theorem mask_bit_false (n : Nat)
    (h0 : n ≠ 0) (h64 : n ≠ 64) (h7 : n ≠ 7) (h8 : n ≠ 8) (h9 : n ≠ 9) (h72 : n ≠ 72) (h63 : n ≠ 63) : maskNat.testBit n = false := by
  simp only [maskNat, Nat.testBit_or,
    Nat.testBit_two_pow_of_ne (Ne.symm h0), Nat.testBit_two_pow_of_ne (Ne.symm h64), Nat.testBit_two_pow_of_ne (Ne.symm h7), Nat.testBit_two_pow_of_ne (Ne.symm h8), Nat.testBit_two_pow_of_ne (Ne.symm h9), Nat.testBit_two_pow_of_ne (Ne.symm h72), Nat.testBit_two_pow_of_ne (Ne.symm h63), Bool.false_or]

private theorem bit_zero (x : UInt256) (h56 : x.toNat ≠ 56)
    (h120 : x.toNat ≠ 120) (h63 : x.toNat ≠ 63)
    (h64 : x.toNat ≠ 64) (h65 : x.toNat ≠ 65) (h128 : x.toNat ≠ 128) (h119 : x.toNat ≠ 119) :
    UInt256.land (UInt256.ofNat 1)
      (UInt256.shiftRight mask (x - UInt256.ofNat 56)) = UInt256.ofNat 0 := by
  set s : UInt256 := x - UInt256.ofNat 56 with hs
  -- the shift amount, related back to the size.  Below 56 the subtraction wraps
  -- and the amount exceeds 256, which shiftRight sends to zero; at or above 56 it
  -- is exactly x - 56, and only 0, 7 and 64 are set in the mask.
  have h56v : (UInt256.ofNat 56).toNat = 56 := by decide
  have hcond : s.toNat =
      if x.toNat < 56 then 2 ^ 256 + x.toNat - 56 else x.toNat - 56 := by
    rw [hs, Word.word_toNat_sub_cond, h56v]
  by_cases hbig : s.toNat ≥ 256
  · simp only [UInt256.shiftRight, if_pos hbig]
    decide
  · have hsmall : s.toNat < 256 := by omega
    have hge : 56 ≤ x.toNat := by
      by_contra hlt
      rw [if_pos (by omega : x.toNat < 56)] at hcond
      have : x.toNat < 2 ^ 256 := x.val.isLt
      omega
    have hval : s.toNat = x.toNat - 56 := by
      rw [hcond, if_neg (by omega)]
    have hsr := Word.shiftRight_toNat mask hsmall
    rw [← Word.word_eq_ofNat_toNat s] at hsr
    apply Word.word_ext
    rw [Word.word_toNat_land, hsr, mask_toNat]
    change 1 &&& (maskNat >>> s.toNat) = 0
    have hb : (maskNat >>> s.toNat).testBit 0 = false := by
      rw [Nat.testBit_shiftRight, Nat.add_zero]
      refine mask_bit_false _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (rw [hval]; omega)
    have h := Nat.two_pow_and (maskNat >>> s.toNat) 0
    simpa [hb] using h

private theorem eq_zero (n : Nat) (hn : n < 2 ^ 256) (x : UInt256)
    (hx : x.toNat ≠ n) : UInt256.eq (UInt256.ofNat n) x = UInt256.ofNat 0 := by
  unfold UInt256.eq
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hn, if_neg (Ne.symm hx)]

theorem flag (x : UInt256) :
    UInt256.isZero (UInt256.land (UInt256.ofNat 1)
        (UInt256.shiftRight mask (x - UInt256.ofNat 56))) =
      UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.ofNat 56) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 120) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 63) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 64) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 65) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 128) x) (UInt256.eq (UInt256.ofNat 119) x))))))) := by
  by_cases h56 : x = UInt256.ofNat 56
  · subst x; decide
  by_cases h120 : x = UInt256.ofNat 120
  · subst x; decide
  by_cases h63 : x = UInt256.ofNat 63
  · subst x; decide
  by_cases h64 : x = UInt256.ofNat 64
  · subst x; decide
  by_cases h65 : x = UInt256.ofNat 65
  · subst x; decide
  by_cases h128 : x = UInt256.ofNat 128
  · subst x; decide
  by_cases h119 : x = UInt256.ofNat 119
  · subst x; decide
  have n56 : x.toNat ≠ 56 := by
    intro h; apply h56; apply Word.word_ext; change x.toNat = 56; exact h
  have n120 : x.toNat ≠ 120 := by
    intro h; apply h120; apply Word.word_ext; change x.toNat = 120; exact h
  have n63 : x.toNat ≠ 63 := by
    intro h; apply h63; apply Word.word_ext; change x.toNat = 63; exact h
  have n64 : x.toNat ≠ 64 := by
    intro h; apply h64; apply Word.word_ext; change x.toNat = 64; exact h
  have n65 : x.toNat ≠ 65 := by
    intro h; apply h65; apply Word.word_ext; change x.toNat = 65; exact h
  have n128 : x.toNat ≠ 128 := by
    intro h; apply h128; apply Word.word_ext; change x.toNat = 128; exact h
  have n119 : x.toNat ≠ 119 := by
    intro h; apply h119; apply Word.word_ext; change x.toNat = 119; exact h
  rw [bit_zero x n56 n120 n63 n64 n65 n128 n119,
    eq_zero 56 (by decide) x n56, eq_zero 120 (by decide) x n120, eq_zero 63 (by decide) x n63, eq_zero 64 (by decide) x n64, eq_zero 65 (by decide) x n65, eq_zero 128 (by decide) x n128, eq_zero 119 (by decide) x n119]
  decide

#print axioms flag
end Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
