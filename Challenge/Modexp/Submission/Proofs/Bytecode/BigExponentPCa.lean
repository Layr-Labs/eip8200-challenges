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
      ([939,940,941,942,943,944,945,946,949,950,951,952,953,954,955,956,957,958,959,961,962,963,964,967,968,970,971,972,974,975,976,977,980,981,982,985,988,991,994] : List Nat)[i - 712]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
