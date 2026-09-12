import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 5 (instructions 1255..1313). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1255..1263, pc 1736..1754. -/
def blk1255 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1083 .JUMPDEST,
   opAt 1084 .POP,
   opAt 1085 .POP,
   pushAt 1086 2 3138,
   pushAt 1087 2 2048,
   pushAt 1088 2 6144,
   pushAt 1089 2 1024,
   pushAt 1090 2 3912,
   opAt 1091 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1092 .JUMPDEST]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1095 .JUMPDEST,
   opAt 1096 (.Dup ⟨4, by decide⟩),
   opAt 1097 (.Dup ⟨1, by decide⟩),
   opAt 1098 .EQ,
   pushAt 1099 2 1545,
   opAt 1100 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1101 2 2102,
   opAt 1102 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1103 .JUMPDEST,
   pushAt 1104 2 1501,
   pushAt 1105 2 1024,
   opAt 1106 (.Dup ⟨0, by decide⟩),
   pushAt 1107 2 1024,
   pushAt 1108 2 3912,
   opAt 1109 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1110 .JUMPDEST,
   opAt 1111 (.Dup ⟨1, by decide⟩),
   opAt 1112 (.Dup ⟨1, by decide⟩),
   opAt 1113 .AND,
   opAt 1114 .ISZERO,
   pushAt 1115 2 1527,
   opAt 1116 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1117 2 1526,
   pushAt 1118 2 1024,
   pushAt 1119 2 2048,
   pushAt 1120 2 1024,
   pushAt 1121 2 3912,
   opAt 1122 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1123 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1124 .JUMPDEST,
   pushAt 1125 1 1,
   opAt 1126 .SHR,
   opAt 1127 (.Dup ⟨0, by decide⟩),
   pushAt 1128 2 1486,
   opAt 1129 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
