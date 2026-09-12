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
    (hi : 775 ≤ i) (hii : i ≤ 824) :
    Artifact.submissionArtifact.instructionPC i =
      ([1041,1042,1043,1044,1045,1046,1049,1050,1051,1053,1054,1055,1058,1059,1060,1061,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1077,1078,1079,1080,1081,1082,1084,1085,1086,1087,1088,1091,1092,1093,1094,1095,1096,1098,1099,1100,1101,1102,1105] : List Nat)[i - 775]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
