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
    (hi : 754 ≤ i) (hii : i ≤ 774) :
    Artifact.submissionArtifact.instructionPC i =
      ([1003,1004,1007,1008,1011,1014,1016,1017,1018,1021,1022,1023,1026,1029,1032,1035,1036,1037,1038,1039,1040] : List Nat)[i - 754]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
