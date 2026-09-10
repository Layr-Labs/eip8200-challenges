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
      ([1034,1035,1036,1037,1038,1039,1042,1043,1044,1046,1047,1048,1051,1052,1053,1054,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1070,1071,1072,1073,1074,1075,1077,1078,1079,1080,1081,1084,1085,1086,1087,1088,1089,1091,1092,1093,1094,1095,1098] : List Nat)[i - 772]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
