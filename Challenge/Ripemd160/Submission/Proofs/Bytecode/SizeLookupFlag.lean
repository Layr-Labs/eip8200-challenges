import Challenge.EvmProof.Word
import Mathlib.Data.Nat.Bitwise
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
open EvmSemantics
open Challenge.EvmProof

/-- Exact size membership for all eight short checked scan paths. -/
def maskNat : Nat := (2 ^ 1) ||| (2 ^ 65) ||| (2 ^ 8) ||| (2 ^ 9) ||| (2 ^ 10) ||| (2 ^ 73) ||| (2 ^ 64) ||| (2 ^ 0)
def mask : UInt256 := UInt256.ofNat maskNat
theorem mask_literal : mask = UInt256.ofNat 9500073197960419084035 := by decide
private theorem mask_toNat : mask.toNat = maskNat := by decide

private theorem mask_bit_false (n : Nat)
    (h1 : n ≠ 1) (h65 : n ≠ 65) (h8 : n ≠ 8) (h9 : n ≠ 9) (h10 : n ≠ 10) (h73 : n ≠ 73) (h64 : n ≠ 64) (h0 : n ≠ 0) : maskNat.testBit n = false := by
  simp only [maskNat, Nat.testBit_or,
    Nat.testBit_two_pow_of_ne (Ne.symm h1), Nat.testBit_two_pow_of_ne (Ne.symm h65), Nat.testBit_two_pow_of_ne (Ne.symm h8), Nat.testBit_two_pow_of_ne (Ne.symm h9), Nat.testBit_two_pow_of_ne (Ne.symm h10), Nat.testBit_two_pow_of_ne (Ne.symm h73), Nat.testBit_two_pow_of_ne (Ne.symm h64), Nat.testBit_two_pow_of_ne (Ne.symm h0), Bool.false_or]

private theorem bit_zero (x : UInt256)
    (h56 : x.toNat ≠ 56) (h120 : x.toNat ≠ 120) (h63 : x.toNat ≠ 63) (h64 : x.toNat ≠ 64) (h65 : x.toNat ≠ 65) (h128 : x.toNat ≠ 128) (h119 : x.toNat ≠ 119) (h55 : x.toNat ≠ 55) :
    UInt256.land (UInt256.ofNat 1)
      (UInt256.shiftRight mask (x - UInt256.ofNat 55)) = UInt256.ofNat 0 := by
  set s : UInt256 := x - UInt256.ofNat 55 with hs
  -- Below 55, word subtraction wraps and the shift exceeds 256.
  have h55v : (UInt256.ofNat 55).toNat = 55 := by decide
  have hcond : s.toNat =
      if x.toNat < 55 then 2 ^ 256 + x.toNat - 55 else x.toNat - 55 := by
    rw [hs, Word.word_toNat_sub_cond, h55v]
  by_cases hbig : s.toNat ≥ 256
  · simp only [UInt256.shiftRight, if_pos hbig]
    decide
  · have hsmall : s.toNat < 256 := by omega
    have hge : 55 ≤ x.toNat := by
      by_contra hlt
      rw [if_pos (by omega : x.toNat < 55)] at hcond
      have : x.toNat < 2 ^ 256 := x.val.isLt
      omega
    have hval : s.toNat = x.toNat - 55 := by
      rw [hcond, if_neg (by omega)]
    have hsr := Word.shiftRight_toNat mask hsmall
    rw [← Word.word_eq_ofNat_toNat s] at hsr
    apply Word.word_ext
    rw [Word.word_toNat_land, hsr, mask_toNat]
    change 1 &&& (maskNat >>> s.toNat) = 0
    have hb : (maskNat >>> s.toNat).testBit 0 = false := by
      rw [Nat.testBit_shiftRight, Nat.add_zero]
      refine mask_bit_false _ ?_  ?_  ?_  ?_  ?_  ?_  ?_  ?_ <;> (rw [hval]; omega)
    have h := Nat.two_pow_and (maskNat >>> s.toNat) 0
    simpa [hb] using h

private theorem eq_zero (n : Nat) (hn : n < 2 ^ 256) (x : UInt256)
    (hx : x.toNat ≠ n) : UInt256.eq (UInt256.ofNat n) x = UInt256.ofNat 0 := by
  unfold UInt256.eq
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hn, if_neg (Ne.symm hx)]

theorem flag (x : UInt256) :
    UInt256.isZero (UInt256.land (UInt256.ofNat 1)
        (UInt256.shiftRight mask (x - UInt256.ofNat 55))) =
      UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.ofNat 56) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 120) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 63) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 64) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 65) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 128) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 119) x) (UInt256.eq (UInt256.ofNat 55) x)))))))) := by
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
  by_cases h55 : x = UInt256.ofNat 55
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
  have n55 : x.toNat ≠ 55 := by
    intro h; apply h55; apply Word.word_ext; change x.toNat = 55; exact h
  rw [bit_zero x n56 n120 n63 n64 n65 n128 n119 n55,
    eq_zero 56 (by decide) x n56, eq_zero 120 (by decide) x n120, eq_zero 63 (by decide) x n63, eq_zero 64 (by decide) x n64, eq_zero 65 (by decide) x n65, eq_zero 128 (by decide) x n128, eq_zero 119 (by decide) x n119, eq_zero 55 (by decide) x n55]
  decide

#print axioms flag
end Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
