import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 3 (instructions 1138..1194). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1138..1147, pc 1533..1554. -/
def blk1138 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1073 .JUMPDEST,
   pushAt 1074 2 5248,
   opAt 1075 .MLOAD,
   pushAt 1076 2 1024,
   pushAt 1077 2 1280,
   opAt 1078 .MCOPY,
   pushAt 1079 2 2972,
   pushAt 1080 2 1280,
   pushAt 1081 2 3396,
   opAt 1082 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1083 .JUMPDEST,
   pushAt 1084 2 1472,
   pushAt 1085 2 1536,
   opAt 1086 (.Dup ⟨0, by decide⟩),
   pushAt 1087 2 1536,
   pushAt 1088 2 4047,
   opAt 1089 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1090 .JUMPDEST,
   opAt 1091 (.Dup ⟨2, by decide⟩),
   opAt 1092 (.Dup ⟨1, by decide⟩),
   opAt 1093 .SHR,
   pushAt 1094 1 1,
   opAt 1095 .AND,
   pushAt 1096 2 256,
   opAt 1097 .MUL,
   pushAt 1098 2 1024,
   opAt 1099 .ADD,
   pushAt 1100 2 2286,
   opAt 1101 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1102 .JUMPDEST,
   opAt 1103 .POP,
   opAt 1104 (.Dup ⟨0, by decide⟩),
   opAt 1105 .ISZERO,
   pushAt 1106 2 1506,
   opAt 1107 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1108 0 0,
   opAt 1109 .NOT,
   opAt 1110 .ADD,
   pushAt 1111 2 1457,
   opAt 1112 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1113 .JUMPDEST,
   opAt 1114 .POP,
   opAt 1115 (.Dup ⟨2, by decide⟩),
   opAt 1116 .ISZERO,
   pushAt 1117 2 3273,
   opAt 1118 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
