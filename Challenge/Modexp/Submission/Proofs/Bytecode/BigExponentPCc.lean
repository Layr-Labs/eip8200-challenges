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
    (hi : 777 ≤ i) (hii : i ≤ 826) :
    Artifact.submissionArtifact.instructionPC i =
      ([1032,1033,1034,1035,1036,1037,1040,1041,1042,1044,1045,1046,1049,1050,1051,1052,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1068,1069,1070,1071,1072,1073,1075,1076,1077,1078,1079,1082,1083,1084,1085,1086,1087,1089,1090,1091,1092,1093,1096] : List Nat)[i - 777]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
