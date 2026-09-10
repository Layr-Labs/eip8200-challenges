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
  [opAt 1090 .JUMPDEST,
   pushAt 1091 2 9344,
   opAt 1092 .MLOAD,
   pushAt 1093 2 4096,
   pushAt 1094 2 5120,
   opAt 1095 .MCOPY,
   pushAt 1096 2 3023,
   pushAt 1097 2 5120,
   pushAt 1098 2 3455,
   opAt 1099 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1100 .JUMPDEST,
   pushAt 1101 2 1484,
   pushAt 1102 2 6144,
   pushAt 1103 2 6144,
   pushAt 1104 2 6144,
   pushAt 1105 2 4140,
   opAt 1106 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1107 .JUMPDEST,
   opAt 1108 (.Dup ⟨2, by decide⟩),
   opAt 1109 (.Dup ⟨1, by decide⟩),
   opAt 1110 .SHR,
   pushAt 1111 1 1,
   opAt 1112 .AND,
   pushAt 1113 2 1024,
   opAt 1114 .MUL,
   pushAt 1115 2 4096,
   opAt 1116 .ADD,
   pushAt 1117 2 2311,
   opAt 1118 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1119 .JUMPDEST,
   opAt 1120 .POP,
   opAt 1121 (.Dup ⟨0, by decide⟩),
   opAt 1122 .ISZERO,
   pushAt 1123 2 1518,
   opAt 1124 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1125 0 0,
   opAt 1126 .NOT,
   opAt 1127 .ADD,
   pushAt 1128 2 1467,
   opAt 1129 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1130 .JUMPDEST,
   opAt 1131 .POP,
   opAt 1132 (.Dup ⟨2, by decide⟩),
   opAt 1133 .ISZERO,
   pushAt 1134 2 1617,
   opAt 1135 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
