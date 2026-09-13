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
  [opAt 1067 .JUMPDEST,
   opAt 1068 (.Dup ⟨1, by decide⟩),
   opAt 1069 .MLOAD,
   opAt 1070 (.Dup ⟨3, by decide⟩),
   opAt 1071 .MLOAD,
   opAt 1072 (.Dup ⟨1, by decide⟩),
   opAt 1073 .ADD,
   opAt 1074 (.Swap ⟨0, by decide⟩),
   opAt 1075 (.Dup ⟨1, by decide⟩),
   opAt 1076 .LT,
   opAt 1077 (.Swap ⟨0, by decide⟩),
   opAt 1078 (.Dup ⟨5, by decide⟩),
   opAt 1079 .ADD,
   opAt 1080 (.Swap ⟨4, by decide⟩),
   opAt 1081 (.Dup ⟨5, by decide⟩),
   opAt 1082 .LT,
   opAt 1083 .OR,
   opAt 1084 (.Swap ⟨3, by decide⟩),
   opAt 1085 (.Dup ⟨1, by decide⟩),
   opAt 1086 .MSTORE,
   pushAt 1087 1 31,
   opAt 1088 .NOT,
   opAt 1089 .ADD,
   opAt 1090 (.Swap ⟨0, by decide⟩),
   pushAt 1091 1 31,
   opAt 1092 .NOT,
   opAt 1093 .ADD,
   opAt 1094 (.Swap ⟨0, by decide⟩),
   opAt 1095 (.Swap ⟨1, by decide⟩),
   pushAt 1096 1 31,
   opAt 1097 .NOT,
   opAt 1098 .ADD,
   opAt 1099 (.Swap ⟨1, by decide⟩),
   pushAt 1100 2 2080,
   opAt 1101 (.Dup ⟨1, by decide⟩),
   opAt 1102 .GT,
   pushAt 1103 2 1522,
   opAt 1104 .JUMPI]

/-- Instructions 1792..1745, pc 2770..2431. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1105 .POP,
   opAt 1106 .POP,
   opAt 1107 .POP,
   pushAt 1108 2 2080,
   opAt 1109 .MSTORE,

   pushAt 1110 2 4337,
   opAt 1111 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
