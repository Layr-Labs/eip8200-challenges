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
  [opAt 1088 .JUMPDEST,
   opAt 1089 .POP,
   opAt 1090 .POP,
   pushAt 1091 2 1481,
   pushAt 1092 2 2048,
   pushAt 1093 2 6144,
   pushAt 1094 2 1024,
   pushAt 1095 2 3862,
   opAt 1096 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1097 .JUMPDEST]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1100 .JUMPDEST,
   opAt 1101 (.Dup ⟨4, by decide⟩),
   opAt 1102 (.Dup ⟨1, by decide⟩),
   opAt 1103 .EQ,
   pushAt 1104 2 1557,
   opAt 1105 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1106 2 2114,
   opAt 1107 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1108 .JUMPDEST,
   pushAt 1109 2 1513,
   pushAt 1110 2 1024,
   opAt 1111 (.Dup ⟨0, by decide⟩),
   pushAt 1112 2 1024,
   pushAt 1113 2 3862,
   opAt 1114 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1115 .JUMPDEST,
   opAt 1116 (.Dup ⟨1, by decide⟩),
   opAt 1117 (.Dup ⟨1, by decide⟩),
   opAt 1118 .AND,
   opAt 1119 .ISZERO,
   pushAt 1120 2 1539,
   opAt 1121 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1122 2 1538,
   pushAt 1123 2 1024,
   pushAt 1124 2 2048,
   pushAt 1125 2 1024,
   pushAt 1126 2 3862,
   opAt 1127 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1128 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1129 .JUMPDEST,
   pushAt 1130 1 1,
   opAt 1131 .SHR,
   opAt 1132 (.Dup ⟨0, by decide⟩),
   pushAt 1133 2 1498,
   opAt 1134 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
