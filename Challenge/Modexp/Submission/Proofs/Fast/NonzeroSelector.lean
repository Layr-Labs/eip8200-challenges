import EvmSemantics.Data.UInt256

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.NonzeroSelector

open EvmSemantics

/-- Comparing zero with a word is the same selector as applying `ISZERO` twice. -/
theorem zero_lt_eq_double_isZero (x : UInt256) :
    UInt256.lt (UInt256.ofNat 0) x = UInt256.isZero (UInt256.isZero x) := by
  have h0 : (UInt256.ofNat 0).toNat = 0 := rfl
  have h1 : (UInt256.ofNat 1).toNat = 1 := rfl
  by_cases hx : x.toNat = 0
  · simp [UInt256.lt, UInt256.isZero, hx, h0, h1]
  · have hxpos : 0 < x.toNat := Nat.pos_of_ne_zero hx
    simp [UInt256.lt, UInt256.isZero, hx, hxpos, h0]

#print axioms zero_lt_eq_double_isZero

end Challenge.Modexp.Submission.Proofs.Fast.NonzeroSelector
