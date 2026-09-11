import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CsubSelectAlgebra
open EvmSemantics

/-- The source-address rewrite holds for every word, not only boolean selectors. -/
theorem offset (flag : UInt256) :
    (8256 : UInt256) + (115792089237316195423570985008687907853269984665640564039457584007913129638848 : UInt256) * flag =
      (8256 : UInt256) - (1088 : UInt256) * flag := by
  change UInt256.mk ((8256 : Fin UInt256.size) +
    (115792089237316195423570985008687907853269984665640564039457584007913129638848 : Fin UInt256.size) * flag.val) =
    UInt256.mk ((8256 : Fin UInt256.size) - (1088 : Fin UInt256.size) * flag.val)
  have hn : (115792089237316195423570985008687907853269984665640564039457584007913129638848 : Fin UInt256.size) =
      -(1088 : Fin UInt256.size) := by decide
  rw [hn, neg_mul, sub_eq_add_neg]

#print axioms offset
end Challenge.Modexp.Submission.Proofs.Fast.CsubSelectAlgebra
