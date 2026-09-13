import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1754..1809). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1754..1788, pc 2380..2769. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1062 .JUMPDEST,
   opAt 1063 (.Dup ⟨1, by decide⟩),
   opAt 1064 .MLOAD,
   opAt 1065 (.Dup ⟨3, by decide⟩),
   opAt 1066 .MLOAD,
   opAt 1067 (.Dup ⟨1, by decide⟩),
   opAt 1068 .ADD,
   opAt 1069 (.Swap ⟨0, by decide⟩),
   opAt 1070 (.Dup ⟨1, by decide⟩),
   opAt 1071 .LT,
   opAt 1072 (.Swap ⟨0, by decide⟩),
   opAt 1073 (.Dup ⟨5, by decide⟩),
   opAt 1074 .ADD,
   opAt 1075 (.Swap ⟨4, by decide⟩),
   opAt 1076 (.Dup ⟨5, by decide⟩),
   opAt 1077 .LT,
   opAt 1078 .OR,
   opAt 1079 (.Swap ⟨3, by decide⟩),
   opAt 1080 (.Dup ⟨1, by decide⟩),
   opAt 1081 .MSTORE,
   pushAt 1082 1 31,
   opAt 1083 .NOT,
   opAt 1084 .ADD,
   opAt 1085 (.Swap ⟨0, by decide⟩),
   pushAt 1086 1 31,
   opAt 1087 .NOT,
   opAt 1088 .ADD,
   opAt 1089 (.Swap ⟨0, by decide⟩),
   opAt 1090 (.Swap ⟨1, by decide⟩),
   pushAt 1091 1 31,
   opAt 1092 .NOT,
   opAt 1093 .ADD,
   opAt 1094 (.Swap ⟨1, by decide⟩),
   pushAt 1095 2 2080,
   opAt 1096 (.Dup ⟨1, by decide⟩),
   opAt 1097 .GT,
   pushAt 1098 2 1510,
   opAt 1099 .JUMPI]

/-- Instructions 1792..1745, pc 2770..2431. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1100 .POP,
   opAt 1101 .POP,
   opAt 1102 .POP,
   pushAt 1103 2 2080,
   opAt 1104 .MSTORE,

   pushAt 1105 2 4349,
   opAt 1106 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
