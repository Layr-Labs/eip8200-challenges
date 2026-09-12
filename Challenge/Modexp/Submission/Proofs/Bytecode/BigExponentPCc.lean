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

@[simp] theorem selectPCs (i : Nat)
    (hi : 733 ≤ i) (hii : i ≤ 782) :
    Artifact.submissionArtifact.instructionPC i =
      ([952,953,954,955,956,957,960,961,962,964,965,966,969,970,971,972,975,976,977,978,979,980,981,982,983,984,985,988,989,990,991,992,993,995,996,997,998,999,1002,1003,1004,1005,1006,1007,1009,1010,1011,1012,1013,1016] : List Nat)[i - 733]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
