import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

/-- Add a word and fold its overflow bit back into the low word. -/
def endCarry (a b : UInt256) : UInt256 :=
  UInt256.gt a (a + b) + (a + b)

/-- Both operands detect the same overflow, including the all-ones result. -/
opaque endCarry_comm (a b : UInt256) : endCarry a b = endCarry b a := by
  apply word_ext
  have ha := word_lt_size a
  have hb := word_lt_size b
  change (UInt256.lt (a + b) a + (a + b)).toNat =
    (UInt256.lt (b + a) b + (b + a)).toNat
  simp only [word_toNat_add, word_toNat_lt]
  split <;> split <;> omega

/-- End-around addition computes the rounded high word from the negated low
word. This identity also covers a zero low word and the all-ones result. -/
theorem endCarry_neg (mm lo : UInt256) :
    endCarry mm (UInt256.ofNat 0 - lo) =
      UInt256.isZero (UInt256.isZero lo) +
        (mm - (lo + UInt256.lt mm lo)) := by
  apply word_ext
  have hm := word_lt_size mm
  have hl := word_lt_size lo
  change ((UInt256.lt (mm + (UInt256.ofNat 0 - lo)) mm) +
    (mm + (UInt256.ofNat 0 - lo))).toNat = _
  simp only [word_toNat_add, word_toNat_sub,
    word_toNat_lt, word_toNat_isZero, word_toNat_ofNat, Nat.zero_mod]
  split <;> split <;> split <;> split <;> omega

/-- The Montgomery inverse makes the retained low accumulator word the
additive inverse of the cancelled product word. -/
theorem cancelled_low (m0 minv t0 : UInt256)
    (hminv : (m0.toNat * minv.toNat + 1) % 2 ^ 256 = 0) :
    t0 = UInt256.ofNat 0 - m0 * (minv * t0) := by
  have hc := c0_spec m0 minv t0 hminv
  have hp := mulHi_spec m0 (minv * t0)
  rw [← hp] at hc
  have ht := word_lt_size t0
  have hl := word_lt_size (m0 * (minv * t0))
  apply word_ext
  simp only [word_toNat_sub, word_toNat_ofNat, Nat.zero_mod]
  omega

/-- The new row head avoids recomputing the cancelled low product with MUL. -/
theorem row_carry (m0 minv t0 : UInt256)
    (hminv : (m0.toNat * minv.toNat + 1) % 2 ^ 256 = 0) :
    endCarry (UInt256.mulMod m0 (minv * t0) maxWord) t0 =
      UInt256.isZero (UInt256.isZero (m0 * (minv * t0))) +
        mulHi m0 (minv * t0) := by
  conv_lhs => arg 2; rw [cancelled_low m0 minv t0 hminv]
  exact endCarry_neg _ _

/-- The selected trace retains the accumulator as the first operand. -/
opaque row_carry_swapped (m0 minv t0 : UInt256)
    (hminv : (m0.toNat * minv.toNat + 1) % 2 ^ 256 = 0) :
    endCarry t0 (UInt256.mulMod m0 (minv * t0) maxWord) =
      UInt256.isZero (UInt256.isZero (m0 * (minv * t0))) +
        mulHi m0 (minv * t0) := by
  rw [endCarry_comm]
  exact row_carry m0 minv t0 hminv

end Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry.row_carry_swapped
