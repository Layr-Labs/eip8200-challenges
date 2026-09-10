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
    (hi : 717 ≤ i) (hii : i ≤ 755) :
    Artifact.submissionArtifact.instructionPC i =
      ([937,938,939,940,941,942,943,944,947,948,949,950,951,952,953,954,955,956,957,959,960,961,962,965,966,968,969,970,972,973,974,975,978,979,980,983,986,989,992] : List Nat)[i - 717]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
