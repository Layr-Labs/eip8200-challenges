import Challenge.EvmProof.Bytes

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Data

open EvmSemantics EvmSemantics.EVM

def checks : List (Nat × UInt256) :=
  [ (0, 32),
    (32, 32),
    (64, 32),
    (96, 5964364953636342908918930162962566239787286640968493902593843747347131818633),
    (128, 21888242871839275222246405745257275088696311157297823662689037894645226208581),
    (160, 21888242871839275222246405745257275088696311157297823662689037894645226208583)
  ]

theorem checks_length : checks.length = 6 := by decide

end Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Data
