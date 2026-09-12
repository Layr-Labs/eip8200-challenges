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
  [opAt 1081 .JUMPDEST,
   opAt 1082 .POP,
   opAt 1083 .POP,
   pushAt 1084 2 1465,
   pushAt 1085 2 2048,
   pushAt 1086 2 6144,
   pushAt 1087 2 1024,
   pushAt 1088 2 3900,
   opAt 1089 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1090 .JUMPDEST]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1093 .JUMPDEST,
   opAt 1094 (.Dup ⟨4, by decide⟩),
   opAt 1095 (.Dup ⟨1, by decide⟩),
   opAt 1096 .EQ,
   pushAt 1097 2 1541,
   opAt 1098 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1099 2 2098,
   opAt 1100 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1101 .JUMPDEST,
   pushAt 1102 2 1497,
   pushAt 1103 2 1024,
   opAt 1104 (.Dup ⟨0, by decide⟩),
   pushAt 1105 2 1024,
   pushAt 1106 2 3900,
   opAt 1107 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1108 .JUMPDEST,
   opAt 1109 (.Dup ⟨1, by decide⟩),
   opAt 1110 (.Dup ⟨1, by decide⟩),
   opAt 1111 .AND,
   opAt 1112 .ISZERO,
   pushAt 1113 2 1523,
   opAt 1114 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1115 2 1522,
   pushAt 1116 2 1024,
   pushAt 1117 2 2048,
   pushAt 1118 2 1024,
   pushAt 1119 2 3900,
   opAt 1120 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1121 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1122 .JUMPDEST,
   pushAt 1123 1 1,
   opAt 1124 .SHR,
   opAt 1125 (.Dup ⟨0, by decide⟩),
   pushAt 1126 2 1482,
   opAt 1127 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
