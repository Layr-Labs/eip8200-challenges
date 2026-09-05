import Challenge.EvmProof.Bytes

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Data

open EvmSemantics EvmSemantics.EVM

def checks : List (Nat × UInt256) :=
  [ (0, 33),
    (32, 1),
    (64, 33),
    (96, 452312848583266388373324160190187140051835877600158453279131187530910662656),
    (128, 2266871685857013885419158128209026732832114290800391293656575918782654971904),
    (160, 48312224427533946512043291035939178167157762805192705886137669566595072)
  ]

theorem checks_length : checks.length = 6 := by decide

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Data
