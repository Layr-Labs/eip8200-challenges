import Challenge.EvmProof.Word
import Mathlib.Data.Nat.Bitwise
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
open EvmSemantics
open Challenge.EvmProof

/-- Exact full-bitmap membership for the eleven short checked paths. -/
def maskNat : Nat := (2 ^ 56) ||| (2 ^ 120) ||| (2 ^ 63) ||| (2 ^ 64) ||| (2 ^ 65) ||| (2 ^ 128) ||| (2 ^ 119) ||| (2 ^ 55) ||| (2 ^ 1) ||| (2 ^ 31) ||| (2 ^ 32)
def mask : UInt256 := UInt256.ofNat maskNat
theorem mask_literal : mask = UInt256.ofNat 342276208914615837337402008677671501826 := by decide
private theorem mask_toNat : mask.toNat = maskNat := by decide
private theorem mask_bit_false (n : Nat)
    (h56 : n ≠ 56) (h120 : n ≠ 120) (h63 : n ≠ 63) (h64 : n ≠ 64) (h65 : n ≠ 65) (h128 : n ≠ 128) (h119 : n ≠ 119) (h55 : n ≠ 55) (h1 : n ≠ 1) (h31 : n ≠ 31) (h32 : n ≠ 32) : maskNat.testBit n = false := by
  simp only [maskNat, Nat.testBit_or,
    Nat.testBit_two_pow_of_ne (Ne.symm h56), Nat.testBit_two_pow_of_ne (Ne.symm h120), Nat.testBit_two_pow_of_ne (Ne.symm h63), Nat.testBit_two_pow_of_ne (Ne.symm h64), Nat.testBit_two_pow_of_ne (Ne.symm h65), Nat.testBit_two_pow_of_ne (Ne.symm h128), Nat.testBit_two_pow_of_ne (Ne.symm h119), Nat.testBit_two_pow_of_ne (Ne.symm h55), Nat.testBit_two_pow_of_ne (Ne.symm h1), Nat.testBit_two_pow_of_ne (Ne.symm h31), Nat.testBit_two_pow_of_ne (Ne.symm h32), Bool.false_or]

private theorem bit_zero (x : UInt256)
    (h56 : x.toNat ≠ 56) (h120 : x.toNat ≠ 120) (h63 : x.toNat ≠ 63) (h64 : x.toNat ≠ 64) (h65 : x.toNat ≠ 65) (h128 : x.toNat ≠ 128) (h119 : x.toNat ≠ 119) (h55 : x.toNat ≠ 55) (h1 : x.toNat ≠ 1) (h31 : x.toNat ≠ 31) (h32 : x.toNat ≠ 32) :
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
      rw [Nat.testBit_shiftRight, Nat.add_zero]
      exact mask_bit_false x.toNat h56 h120 h63 h64 h65 h128 h119 h55 h1 h31 h32
    have h := Nat.two_pow_and (maskNat >>> x.toNat) 0
    simpa [hb] using h

private theorem eq_zero (n : Nat) (hn : n < 2 ^ 256) (x : UInt256)
    (hx : x.toNat ≠ n) : UInt256.eq (UInt256.ofNat n) x = UInt256.ofNat 0 := by
  unfold UInt256.eq
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hn, if_neg (Ne.symm hx)]

theorem flag (x : UInt256) :
    UInt256.isZero (UInt256.land (UInt256.ofNat 1) (UInt256.shiftRight mask x)) =
      UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.ofNat 56) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 120) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 63) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 64) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 65) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 128) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 119) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 55) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 1) x) (UInt256.lor (UInt256.eq (UInt256.ofNat 31) x) (UInt256.eq (UInt256.ofNat 32) x))))))))))) := by
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
  by_cases h1 : x = UInt256.ofNat 1
  · subst x; decide
  by_cases h31 : x = UInt256.ofNat 31
  · subst x; decide
  by_cases h32 : x = UInt256.ofNat 32
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
  have n1 : x.toNat ≠ 1 := by
    intro h; apply h1; apply Word.word_ext; change x.toNat = 1; exact h
  have n31 : x.toNat ≠ 31 := by
    intro h; apply h31; apply Word.word_ext; change x.toNat = 31; exact h
  have n32 : x.toNat ≠ 32 := by
    intro h; apply h32; apply Word.word_ext; change x.toNat = 32; exact h
  rw [bit_zero x n56 n120 n63 n64 n65 n128 n119 n55 n1 n31 n32,
    eq_zero 56 (by decide) x n56, eq_zero 120 (by decide) x n120, eq_zero 63 (by decide) x n63, eq_zero 64 (by decide) x n64, eq_zero 65 (by decide) x n65, eq_zero 128 (by decide) x n128, eq_zero 119 (by decide) x n119, eq_zero 55 (by decide) x n55, eq_zero 1 (by decide) x n1, eq_zero 31 (by decide) x n31, eq_zero 32 (by decide) x n32]
  decide

#print axioms flag
end Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
