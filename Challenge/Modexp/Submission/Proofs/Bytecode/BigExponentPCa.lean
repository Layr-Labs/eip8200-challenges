import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! # Program-counter tables for the multi-limb exponentiation path

Kept in a module with minimal imports: `interval_cases … <;> decide` over these
ranges is elaborated far more cheaply without the whole `Big*` simp environment
in scope.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp

@[simp] theorem exponentPCs (i : Nat)
    (hi : 640 ≤ i) (hii : i ≤ 678) :
    Artifact.submissionArtifact.instructionPC i =
      ([814,815,816,817,818,819,820,821,824,825,826,827,828,829,830,831,832,833,834,836,837,838,839,842,843,845,846,847,849,850,851,852,855,856,857,860,863,864,867] : List Nat)[i - 640]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
