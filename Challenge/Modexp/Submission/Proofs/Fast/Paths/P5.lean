import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 5 (instructions 1303..1313). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1303..1311, pc 1784..1754. -/
def blk1255 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1118 .JUMPDEST,
   opAt 1119 .POP,
   opAt 1120 .POP,
   pushAt 1121 2 1517,
   pushAt 1122 2 2048,
   pushAt 1123 2 6144,
   pushAt 1124 2 1024,
   pushAt 1125 2 4055,
   opAt 1126 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1127 .JUMPDEST]

/-- Instructions 1320..1278, pc 1817..1825. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1130 .JUMPDEST,
   opAt 1131 (.Dup ⟨4, by decide⟩),
   opAt 1132 (.Dup ⟨1, by decide⟩),
   opAt 1133 .EQ,
   pushAt 1134 2 1593,
   opAt 1135 .JUMPI]

/-- Instructions 1327..1334, pc 1826..1835. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1136 2 2150,
   opAt 1137 .JUMP]

/-- Instructions 1335..1341, pc 1837..1853. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1138 .JUMPDEST,
   pushAt 1139 2 1549,
   pushAt 1140 2 1024,
   opAt 1141 (.Dup ⟨0, by decide⟩),
   pushAt 1142 2 1024,
   pushAt 1143 2 4055,
   opAt 1144 .JUMP]

/-- Instructions 1342..1348, pc 1854..1862. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1145 .JUMPDEST,
   opAt 1146 (.Dup ⟨1, by decide⟩),
   opAt 1147 (.Dup ⟨1, by decide⟩),
   opAt 1148 .AND,
   opAt 1149 .ISZERO,
   pushAt 1150 2 1575,
   opAt 1151 .JUMPI]

/-- Instructions 1349..1306, pc 1863..1878. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1152 2 1574,
   pushAt 1153 2 1024,
   pushAt 1154 2 2048,
   pushAt 1155 2 1024,
   pushAt 1156 2 4055,
   opAt 1157 .JUMP]

/-- Instructions 1307..1307, pc 1879..1879. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1158 .JUMPDEST]

/-- Instructions 1356..1313, pc 1832..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1159 .JUMPDEST,
   pushAt 1160 1 1,
   opAt 1161 .SHR,
   opAt 1162 (.Dup ⟨0, by decide⟩),
   pushAt 1163 2 1534,
   opAt 1164 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
