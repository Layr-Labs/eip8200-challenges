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
  [opAt 1066 .JUMPDEST,
   pushAt 1067 2 2688,
   opAt 1068 .MLOAD,
   pushAt 1069 2 1024,
   pushAt 1070 2 1280,
   opAt 1071 .MCOPY,
   pushAt 1072 2 2972,
   pushAt 1073 2 1280,
   pushAt 1074 2 3333,
   opAt 1075 .JUMP]

/-- Instructions 1282..1202, pc 1680..1692. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1289..1295, pc 1569..1662. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1076 .JUMPDEST,
   pushAt 1077 2 1467,
   pushAt 1078 2 1536,
   opAt 1079 (.Dup ⟨0, by decide⟩),
   pushAt 1080 2 1536,
   pushAt 1081 2 4092,
   opAt 1082 .JUMP]

/-- Instructions 1296..1307, pc 1713..1599. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1083 .JUMPDEST,
   opAt 1084 (.Dup ⟨2, by decide⟩),
   opAt 1085 (.Dup ⟨1, by decide⟩),
   opAt 1086 .SHR,
   pushAt 1087 1 1,
   opAt 1088 .AND,
   pushAt 1089 2 256,
   opAt 1090 .MUL,
   pushAt 1091 2 1024,
   opAt 1092 .ADD,
   pushAt 1093 2 2278,
   opAt 1094 .JUMP]

/-- Instructions 1178..1269, pc 1692..1749. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1095 .JUMPDEST,
   opAt 1096 .POP,
   opAt 1097 (.Dup ⟨0, by decide⟩),
   opAt 1098 .ISZERO,
   pushAt 1099 2 1501,
   opAt 1100 .JUMPI]

/-- Instructions 1184..1188, pc 1750..1760. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1101 0 0,
   opAt 1102 .NOT,
   opAt 1103 .ADD,
   pushAt 1104 2 1452,
   opAt 1105 .JUMP]

/-- Instructions 1323..1324, pc 1758..1717. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1106 .JUMPDEST,
   opAt 1107 .POP,
   opAt 1108 (.Dup ⟨2, by decide⟩),
   opAt 1109 .ISZERO,
   pushAt 1110 2 3216,
   opAt 1111 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
