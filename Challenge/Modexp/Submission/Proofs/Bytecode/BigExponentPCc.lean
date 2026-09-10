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
    (hi : 772 ≤ i) (hii : i ≤ 821) :
    Artifact.submissionArtifact.instructionPC i =
      ([1001,1002,1003,1004,1005,1006,1009,1010,1011,1013,1014,1015,1018,1019,1020,1021,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1037,1038,1039,1040,1041,1042,1044,1045,1046,1047,1048,1051,1052,1053,1054,1055,1056,1058,1059,1060,1061,1062,1065] : List Nat)[i - 772]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
