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
    (hi : 751 ≤ i) (hii : i ≤ 771) :
    Artifact.submissionArtifact.instructionPC i =
      ([995,996,999,1000,1003,1006,1009,1010,1011,1014,1015,1016,1019,1022,1025,1028,1029,1030,1031,1032,1033] : List Nat)[i - 751]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
