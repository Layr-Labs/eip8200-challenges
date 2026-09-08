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
    (hi : 774 ≤ i) (hii : i ≤ 823) :
    Artifact.submissionArtifact.instructionPC i =
      [1035,1036,1037,1038,1039,1040,1043,1044,1045,1047,1048,1049,1052,1053,1054,1055,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1071,1072,1073,1074,1075,1076,1078,1079,1080,1081,1082,1085,1086,1087,1088,1089,1090,1092,1093,1094,1095,1096,1099][i - 774]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
