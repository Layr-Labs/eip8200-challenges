import Challenge.EvmProof.Word
import Mathlib.Tactic

set_option warningAsError true
set_option maxRecDepth 40000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareWords
open EvmSemantics
open Challenge.EvmProof.Word

def doubled (x c : UInt256) : UInt256 := UInt256.lor (x+x) c
def highBit (x : UInt256) : UInt256 := UInt256.shiftRight x (UInt256.ofNat 255)
def clearBit (x : UInt256) : UInt256 := UInt256.land x (UInt256.lnot 1)

/-- OR inserts the one-bit carry into an even word without an extra carry. -/
theorem even_or (x c : Nat) (hc : c < 2) :
    (2*x ||| c) = 2*x+c := by
  simpa only [show (2^1 : Nat) = 2 from rfl, Nat.mul_comm x 2] using
    (Nat.two_pow_add_eq_or_of_lt (i := 1) hc x).symm

theorem doubled_spec (x c : UInt256) (hc : c.toNat < 2) :
    (highBit x).toNat * 2^256 + (doubled x c).toNat = 2*x.toNat+c.toNat := by
  have hx := x.val.isLt
  have hd := Nat.mod_add_div x.toNat (2^255)
  have hm := Nat.mod_lt x.toNat (show 0 < 2^255 by decide)
  have heven : (x.toNat + x.toNat) % 2^256 = 2*(x.toNat % 2^255) := by omega
  rw [doubled, word_toNat_lor, word_toNat_add, heven, even_or _ _ hc]
  have hhigh : (highBit x).toNat = x.toNat / 2^255 := by
    simpa only [highBit, Nat.shiftRight_eq_div_pow] using
      shiftRight_toNat x (show 255 < 256 by decide)
  rw [hhigh]
  omega

theorem highBit_lt_two (x : UInt256) : (highBit x).toNat < 2 := by
  have hhigh : (highBit x).toNat = x.toNat / 2^255 := by
    simpa only [highBit, Nat.shiftRight_eq_div_pow] using
      shiftRight_toNat x (show 255 < 256 by decide)
  have hx := x.val.isLt
  change x.toNat < 2^256 at hx
  rw [hhigh]
  omega

/-- Clearing bit zero rounds the doubled high suffix down to an even value. -/
theorem clearBit_toNat (x : UInt256) : (clearBit x).toNat = x.toNat / 2 * 2 := by
  have hmask : (UInt256.lnot 1).toNat = 2^256-2 := by decide
  rw [clearBit, word_toNat_land, hmask]
  have hd := Nat.and_div_two_pow (a := x.toNat) (b := 2^256-2) (n := 1)
  have hm := Nat.and_mod_two_pow (a := x.toNat) (b := 2^256-2) (n := 1)
  have hx := x.val.isLt
  change x.toNat < 2^256 at hx
  have hhalf : x.toNat/2 < 2^255 := by omega
  norm_num only [Nat.reducePow, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod] at hd hm
  have hfull : x.toNat/2 &&& (2^255-1) = x.toNat/2 :=
    Nat.and_two_pow_sub_one_of_lt_two_pow hhalf
  norm_num only [Nat.reducePow, Nat.reduceSub] at hfull
  rw [hfull] at hd
  simp only [Nat.and_zero] at hm
  have hsplit := Nat.mod_add_div (x.toNat &&& (2^256-2)) 2
  norm_num only [Nat.reducePow, Nat.reduceSub] at hsplit ⊢
  omega

#print axioms doubled_spec
#print axioms clearBit_toNat
end Challenge.Modexp.Submission.Proofs.Fast.SquareWords
