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
    (hi : 752 ≤ i) (hii : i ≤ 772) :
    Artifact.submissionArtifact.instructionPC i =
      [996,997,1000,1001,1004,1007,1010,1011,1012,1015,1016,1017,1020,1023,1026,1029,1030,1031,1032,1033,1034][i - 752]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
