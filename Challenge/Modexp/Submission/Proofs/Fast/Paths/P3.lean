import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 3 (instructions 1186..1324). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1186..1229, pc 1610..1679. -/
def blk1138 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1065 .JUMPDEST,
   pushAt 1066 2 2688,
   opAt 1067 .MLOAD,
   pushAt 1068 2 1024,
   pushAt 1069 2 1280,
   opAt 1070 .MCOPY,
   pushAt 1071 2 2972,
   pushAt 1072 2 1280,
   pushAt 1073 2 3333,
   opAt 1074 .JUMP]

/-- Instructions 1282..1202, pc 1680..1692. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1289..1295, pc 1569..1662. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1075 .JUMPDEST,
   pushAt 1076 2 1467,
   pushAt 1077 2 1536,
   opAt 1078 (.Dup ⟨0, by decide⟩),
   pushAt 1079 2 1536,
   pushAt 1080 2 4092,
   opAt 1081 .JUMP]

/-- Instructions 1296..1307, pc 1713..1599. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1082 .JUMPDEST,
   opAt 1083 (.Dup ⟨2, by decide⟩),
   opAt 1084 (.Dup ⟨1, by decide⟩),
   opAt 1085 .SHR,
   pushAt 1086 1 1,
   opAt 1087 .AND,
   pushAt 1088 2 256,
   opAt 1089 .MUL,
   pushAt 1090 2 1024,
   opAt 1091 .ADD,
   pushAt 1092 2 2278,
   opAt 1093 .JUMP]

/-- Instructions 1178..1269, pc 1692..1749. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1094 .JUMPDEST,
   opAt 1095 .POP,
   opAt 1096 (.Dup ⟨0, by decide⟩),
   opAt 1097 .ISZERO,
   pushAt 1098 2 1501,
   opAt 1099 .JUMPI]

/-- Instructions 1184..1188, pc 1750..1760. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1100 0 0,
   opAt 1101 .NOT,
   opAt 1102 .ADD,
   pushAt 1103 2 1452,
   opAt 1104 .JUMP]

/-- Instructions 1323..1324, pc 1758..1717. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1105 .JUMPDEST,
   opAt 1106 .POP,
   opAt 1107 (.Dup ⟨2, by decide⟩),
   opAt 1108 .ISZERO,
   pushAt 1109 2 3216,
   opAt 1110 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
