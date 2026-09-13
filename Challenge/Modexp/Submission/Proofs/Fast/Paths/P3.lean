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
  [opAt 1070 .JUMPDEST,
   pushAt 1071 2 2688,
   opAt 1072 .MLOAD,
   pushAt 1073 2 1024,
   pushAt 1074 2 1280,
   opAt 1075 .MCOPY,
   pushAt 1076 2 2972,
   pushAt 1077 2 1280,
   pushAt 1078 2 3333,
   opAt 1079 .JUMP]

/-- Instructions 1282..1202, pc 1680..1692. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1289..1295, pc 1569..1662. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1080 .JUMPDEST,
   pushAt 1081 2 1467,
   pushAt 1082 2 1536,
   opAt 1083 (.Dup ⟨0, by decide⟩),
   pushAt 1084 2 1536,
   pushAt 1085 2 4086,
   opAt 1086 .JUMP]

/-- Instructions 1296..1307, pc 1713..1599. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1087 .JUMPDEST,
   opAt 1088 (.Dup ⟨2, by decide⟩),
   opAt 1089 (.Dup ⟨1, by decide⟩),
   opAt 1090 .SHR,
   pushAt 1091 1 1,
   opAt 1092 .AND,
   pushAt 1093 2 256,
   opAt 1094 .MUL,
   pushAt 1095 2 1024,
   opAt 1096 .ADD,
   pushAt 1097 2 2278,
   opAt 1098 .JUMP]

/-- Instructions 1178..1269, pc 1692..1749. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1099 .JUMPDEST,
   opAt 1100 .POP,
   opAt 1101 (.Dup ⟨0, by decide⟩),
   opAt 1102 .ISZERO,
   pushAt 1103 2 1501,
   opAt 1104 .JUMPI]

/-- Instructions 1184..1188, pc 1750..1760. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1105 0 0,
   opAt 1106 .NOT,
   opAt 1107 .ADD,
   pushAt 1108 2 1452,
   opAt 1109 .JUMP]

/-- Instructions 1323..1324, pc 1758..1717. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1110 .JUMPDEST,
   opAt 1111 .POP,
   opAt 1112 (.Dup ⟨2, by decide⟩),
   opAt 1113 .ISZERO,
   pushAt 1114 2 3216,
   opAt 1115 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
