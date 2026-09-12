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
    (hi : 738 ≤ i) (hii : i ≤ 787) :
    Artifact.submissionArtifact.instructionPC i =
      ([959,960,961,962,963,964,967,968,969,971,972,973,976,977,978,979,982,983,984,985,986,987,988,989,990,991,992,995,996,997,998,999,1000,1002,1003,1004,1005,1006,1009,1010,1011,1012,1013,1014,1016,1017,1018,1019,1020,1023] : List Nat)[i - 738]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
