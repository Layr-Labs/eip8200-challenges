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
  [opAt 1059 .JUMPDEST,
   opAt 1060 (.Dup ⟨1, by decide⟩),
   opAt 1061 .MLOAD,
   opAt 1062 (.Dup ⟨3, by decide⟩),
   opAt 1063 .MLOAD,
   opAt 1064 (.Dup ⟨1, by decide⟩),
   opAt 1065 .ADD,
   opAt 1066 (.Swap ⟨0, by decide⟩),
   opAt 1067 (.Dup ⟨1, by decide⟩),
   opAt 1068 .LT,
   opAt 1069 (.Swap ⟨0, by decide⟩),
   opAt 1070 (.Dup ⟨5, by decide⟩),
   opAt 1071 .ADD,
   opAt 1072 (.Swap ⟨4, by decide⟩),
   opAt 1073 (.Dup ⟨5, by decide⟩),
   opAt 1074 .LT,
   opAt 1075 .OR,
   opAt 1076 (.Swap ⟨3, by decide⟩),
   opAt 1077 (.Dup ⟨1, by decide⟩),
   opAt 1078 .MSTORE,
   pushAt 1079 1 31,
   opAt 1080 .NOT,
   opAt 1081 .ADD,
   opAt 1082 (.Swap ⟨0, by decide⟩),
   pushAt 1083 1 31,
   opAt 1084 .NOT,
   opAt 1085 .ADD,
   opAt 1086 (.Swap ⟨0, by decide⟩),
   opAt 1087 (.Swap ⟨1, by decide⟩),
   pushAt 1088 1 31,
   opAt 1089 .NOT,
   opAt 1090 .ADD,
   opAt 1091 (.Swap ⟨1, by decide⟩),
   pushAt 1092 2 2080,
   opAt 1093 (.Dup ⟨1, by decide⟩),
   opAt 1094 .GT,
   pushAt 1095 2 1505,
   opAt 1096 .JUMPI]

/-- Instructions 1792..1745, pc 2770..2431. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1097 .POP,
   opAt 1098 .POP,
   opAt 1099 .POP,
   pushAt 1100 2 2080,
   opAt 1101 .MSTORE,
   pushAt 1102 2 4335,
   opAt 1103 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
