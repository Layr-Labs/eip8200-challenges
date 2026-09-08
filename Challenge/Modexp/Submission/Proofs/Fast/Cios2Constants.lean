import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Constants

open EvmSemantics

/-- The compact pointer-decrement constant, checked once as a closed word fact. -/
@[simp] theorem notThirtyOne : UInt256.lnot (31 : UInt256) =
    UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide

/-- The compact full-word multiplication modulus. -/
@[simp] theorem notZero : UInt256.lnot (0 : UInt256) = Monpro.maxWord := by
  decide

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Constants
