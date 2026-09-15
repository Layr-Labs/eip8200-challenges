import Challenge.Modexp.Submission.Proofs.Fast.CarryIface
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowGas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! The row bundle of the multiply composition, instantiated with WP-K's stage-2 block traces. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryIface

open Challenge.Modexp.Submission.Proofs.Fast

/-- WP-K's `CarryRowGas` block traces of one multiply row. -/
def rowLemmas : RowLemmas where
  gasSteps_out := CarryRowGas.gasSteps_out
  gasSteps_commonFirst := CarryRowGas.gasSteps_commonFirst
  gasSteps_l1MulFour := CarryRowGas.gasSteps_l1MulFour
  gasSteps_l1MulEight := CarryRowGas.gasSteps_l1MulEight
  gasSteps_mid := CarryRowGas.gasSteps_mid
  gasSteps_l2Four := CarryRowGas.gasSteps_l2Four
  gasSteps_l2Eight := CarryRowGas.gasSteps_l2Eight
  gasSteps_tailNext := CarryRowGas.gasSteps_tailNext
  gasSteps_tailLast := CarryRowGas.gasSteps_tailLast

end Challenge.Modexp.Submission.Proofs.Fast.CarryIface
