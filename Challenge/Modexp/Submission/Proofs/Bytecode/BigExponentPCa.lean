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
    (hi : 678 ≤ i) (hii : i ≤ 716) :
    Artifact.submissionArtifact.instructionPC i =
      ([867,868,869,870,871,872,873,874,877,878,879,880,881,882,883,884,885,886,887,889,890,891,892,895,896,898,899,900,902,903,904,905,908,909,910,913,916,917,920] : List Nat)[i - 678]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
