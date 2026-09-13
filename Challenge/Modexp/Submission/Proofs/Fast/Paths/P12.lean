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
  [opAt 1060 .JUMPDEST,
   opAt 1061 (.Dup ⟨1, by decide⟩),
   opAt 1062 .MLOAD,
   opAt 1063 (.Dup ⟨3, by decide⟩),
   opAt 1064 .MLOAD,
   opAt 1065 (.Dup ⟨1, by decide⟩),
   opAt 1066 .ADD,
   opAt 1067 (.Swap ⟨0, by decide⟩),
   opAt 1068 (.Dup ⟨1, by decide⟩),
   opAt 1069 .LT,
   opAt 1070 (.Swap ⟨0, by decide⟩),
   opAt 1071 (.Dup ⟨5, by decide⟩),
   opAt 1072 .ADD,
   opAt 1073 (.Swap ⟨4, by decide⟩),
   opAt 1074 (.Dup ⟨5, by decide⟩),
   opAt 1075 .LT,
   opAt 1076 .OR,
   opAt 1077 (.Swap ⟨3, by decide⟩),
   opAt 1078 (.Dup ⟨1, by decide⟩),
   opAt 1079 .MSTORE,
   pushAt 1080 1 31,
   opAt 1081 .NOT,
   opAt 1082 .ADD,
   opAt 1083 (.Swap ⟨0, by decide⟩),
   pushAt 1084 1 31,
   opAt 1085 .NOT,
   opAt 1086 .ADD,
   opAt 1087 (.Swap ⟨0, by decide⟩),
   opAt 1088 (.Swap ⟨1, by decide⟩),
   pushAt 1089 1 31,
   opAt 1090 .NOT,
   opAt 1091 .ADD,
   opAt 1092 (.Swap ⟨1, by decide⟩),
   pushAt 1093 2 2080,
   opAt 1094 (.Dup ⟨1, by decide⟩),
   opAt 1095 .GT,
   pushAt 1096 2 1506,
   opAt 1097 .JUMPI]

/-- Instructions 1792..1745, pc 2770..2431. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1098 .POP,
   opAt 1099 .POP,
   opAt 1100 .POP,
   pushAt 1101 2 2080,
   opAt 1102 .MSTORE,
   pushAt 1103 2 4336,
   opAt 1104 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
