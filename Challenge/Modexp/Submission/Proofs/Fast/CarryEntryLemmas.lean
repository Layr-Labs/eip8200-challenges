import Challenge.Modexp.Submission.Proofs.Fast.CarryIface

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! The entry bundle of the multiply composition, instantiated with WP-K2's kernel-entry traces. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryIface

open Challenge.Modexp.Submission.Proofs.Fast

/-- WP-K2's `Cios2Dispatch` traces: `mul entry`, `common` + `setup`, `common` fallback. -/
def entryLemmas : EntryLemmas where
  gasSteps_mulEntry := Cios2Dispatch.gasSteps_mulEntry
  gasSteps_commonSetup := Cios2Dispatch.gasSteps_commonSetup
  gasSteps_commonFallback := Cios2Dispatch.gasSteps_commonFallback

end Challenge.Modexp.Submission.Proofs.Fast.CarryIface
