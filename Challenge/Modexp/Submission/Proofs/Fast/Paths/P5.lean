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
  [opAt 1101 .JUMPDEST,
   opAt 1102 .POP,
   opAt 1103 .POP,
   pushAt 1104 2 1502,
   pushAt 1105 2 512,
   pushAt 1106 2 1536,
   pushAt 1107 2 256,
   pushAt 1108 2 3920,
   opAt 1109 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1110 .JUMPDEST]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1113 .JUMPDEST,
   opAt 1114 (.Dup ⟨4, by decide⟩),
   opAt 1115 (.Dup ⟨1, by decide⟩),
   opAt 1116 .EQ,
   pushAt 1117 2 1578,
   opAt 1118 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1119 2 2143,
   opAt 1120 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1121 .JUMPDEST,
   pushAt 1122 2 1534,
   pushAt 1123 2 256,
   opAt 1124 (.Dup ⟨0, by decide⟩),
   pushAt 1125 2 256,
   pushAt 1126 2 3920,
   opAt 1127 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1128 .JUMPDEST,
   opAt 1129 (.Dup ⟨1, by decide⟩),
   opAt 1130 (.Dup ⟨1, by decide⟩),
   opAt 1131 .AND,
   opAt 1132 .ISZERO,
   pushAt 1133 2 1560,
   opAt 1134 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1135 2 1559,
   pushAt 1136 2 256,
   pushAt 1137 2 512,
   pushAt 1138 2 256,
   pushAt 1139 2 3920,
   opAt 1140 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1141 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1142 .JUMPDEST,
   pushAt 1143 1 1,
   opAt 1144 .SHR,
   opAt 1145 (.Dup ⟨0, by decide⟩),
   pushAt 1146 2 1519,
   opAt 1147 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
