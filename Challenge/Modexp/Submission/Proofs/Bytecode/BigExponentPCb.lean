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

@[simp] theorem exponentMidPCs (i : Nat)
    (hi : 717 ≤ i) (hii : i ≤ 737) :
    Artifact.submissionArtifact.instructionPC i =
      ([921,922,925,926,929,932,934,935,936,939,940,941,944,947,950,953,954,955,956,957,958] : List Nat)[i - 717]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
