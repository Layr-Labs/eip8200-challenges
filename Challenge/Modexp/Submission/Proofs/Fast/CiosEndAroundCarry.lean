import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

/-- Add a word and fold its overflow bit back into the low word. -/
def endCarry (a b : UInt256) : UInt256 :=
  UInt256.gt a (a + b) + (a + b)

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

end Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry.row_carry
