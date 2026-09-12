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
    (hi : 673 ≤ i) (hii : i ≤ 711) :
    Artifact.submissionArtifact.instructionPC i =
      ([860,861,862,863,864,865,866,867,870,871,872,873,874,875,876,877,878,879,880,882,883,884,885,888,889,891,892,893,895,896,897,898,901,902,903,906,909,910,913] : List Nat)[i - 673]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
