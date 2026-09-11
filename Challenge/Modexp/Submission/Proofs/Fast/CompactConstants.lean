import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CompactConstants

open EvmSemantics

/-- Closed word identities for the compact constants in cold paths.
These are used locally by trace proofs and carry no global simp attributes. -/
theorem notZero : UInt256.lnot (0 : UInt256) =
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256) := by
  decide

theorem notZeroStruct : UInt256.lnot ({ val := 0 } : UInt256) =
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 : UInt256) := by
  decide

theorem notThirtyOne : UInt256.lnot (31 : UInt256) = UInt256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide

theorem not1087 : UInt256.lnot (1087 : UInt256) =
    (115792089237316195423570985008687907853269984665640564039457584007913129638848 : UInt256) := by
  decide

end Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
