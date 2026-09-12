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
  [opAt 1072 .JUMPDEST,
   pushAt 1073 2 9344,
   opAt 1074 .MLOAD,
   pushAt 1075 2 4096,
   pushAt 1076 2 5120,
   opAt 1077 .MCOPY,
   pushAt 1078 2 2972,
   pushAt 1079 2 5120,
   pushAt 1080 2 3396,
   opAt 1081 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1082 .JUMPDEST,
   pushAt 1083 2 1472,
   pushAt 1084 2 6144,
   opAt 1085 (.Dup ⟨0, by decide⟩),
   pushAt 1086 2 6144,
   pushAt 1087 2 4047,
   opAt 1088 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1089 .JUMPDEST,
   opAt 1090 (.Dup ⟨2, by decide⟩),
   opAt 1091 (.Dup ⟨1, by decide⟩),
   opAt 1092 .SHR,
   pushAt 1093 1 1,
   opAt 1094 .AND,
   pushAt 1095 2 1024,
   opAt 1096 .MUL,
   pushAt 1097 2 4096,
   opAt 1098 .ADD,
   pushAt 1099 2 2286,
   opAt 1100 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1101 .JUMPDEST,
   opAt 1102 .POP,
   opAt 1103 (.Dup ⟨0, by decide⟩),
   opAt 1104 .ISZERO,
   pushAt 1105 2 1506,
   opAt 1106 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1107 0 0,
   opAt 1108 .NOT,
   opAt 1109 .ADD,
   pushAt 1110 2 1457,
   opAt 1111 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1112 .JUMPDEST,
   opAt 1113 .POP,
   opAt 1114 (.Dup ⟨2, by decide⟩),
   opAt 1115 .ISZERO,
   pushAt 1116 2 3273,
   opAt 1117 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
