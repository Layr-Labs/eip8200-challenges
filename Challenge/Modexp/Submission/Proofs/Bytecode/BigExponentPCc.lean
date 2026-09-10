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
    (hi : 757 ≤ i) (hii : i ≤ 806) :
    Artifact.submissionArtifact.instructionPC i =
      ([986,987,988,989,990,991,994,995,996,998,999,1000,1003,1004,1005,1006,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1022,1023,1024,1025,1026,1027,1029,1030,1031,1032,1033,1036,1037,1038,1039,1040,1041,1043,1044,1045,1046,1047,1050] : List Nat)[i - 757]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
