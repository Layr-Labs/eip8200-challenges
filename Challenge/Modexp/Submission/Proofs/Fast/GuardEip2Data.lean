import Challenge.EvmProof.Bytes

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Data

open EvmSemantics EvmSemantics.EVM

def checks : List (Nat × UInt256) :=
  [
    (0, 0),
    (32, 32),
    (64, 32),
    (96, 115792089237316195423570985008687907853269984665640564039457584007908834671662),
    (128, 115792089237316195423570985008687907853269984665640564039457584007908834671663)
  ]

theorem checks_length : checks.length = 5 := by decide

end Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Data
