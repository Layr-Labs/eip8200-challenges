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
    (hi : 712 ≤ i) (hii : i ≤ 750) :
    Artifact.submissionArtifact.instructionPC i =
      ([907,908,909,910,911,912,913,914,917,918,919,920,921,922,923,924,925,926,927,929,930,931,932,935,936,938,939,940,942,943,944,945,948,949,950,953,956,959,962] : List Nat)[i - 712]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
