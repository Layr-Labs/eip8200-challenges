import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 5 (instructions 1385..1395). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1385..1393, pc 1866..1836. -/
def blk1255 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1156 .JUMPDEST,
   opAt 1157 .POP,
   opAt 1158 .POP,
   pushAt 1159 2 3275,
   pushAt 1160 2 512,
   pushAt 1161 2 1536,
   pushAt 1162 2 256,
   pushAt 1163 2 4151,
   opAt 1164 .JUMP]

/-- Instructions 1346..1346, pc 1837..1837. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1165 .JUMPDEST]

/-- Instructions 1402..1360, pc 1899..1907. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1168 .JUMPDEST,
   opAt 1169 (.Dup ⟨4, by decide⟩),
   opAt 1170 (.Dup ⟨1, by decide⟩),
   opAt 1171 .EQ,
   pushAt 1172 2 1675,
   opAt 1173 .JUMPI]

/-- Instructions 1409..1416, pc 1908..1917. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1174 2 2232,
   opAt 1175 .JUMP]

/-- Instructions 1417..1423, pc 1919..1935. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1176 .JUMPDEST,
   pushAt 1177 2 1631,
   pushAt 1178 2 256,
   opAt 1179 (.Dup ⟨0, by decide⟩),
   pushAt 1180 2 256,
   pushAt 1181 2 4151,
   opAt 1182 .JUMP]

/-- Instructions 1424..1430, pc 1936..1944. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1183 .JUMPDEST,
   opAt 1184 (.Dup ⟨1, by decide⟩),
   opAt 1185 (.Dup ⟨1, by decide⟩),
   opAt 1186 .AND,
   opAt 1187 .ISZERO,
   pushAt 1188 2 1657,
   opAt 1189 .JUMPI]

/-- Instructions 1431..1388, pc 1945..1960. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1190 2 1656,
   pushAt 1191 2 256,
   pushAt 1192 2 512,
   pushAt 1193 2 256,
   pushAt 1194 2 4151,
   opAt 1195 .JUMP]

/-- Instructions 1389..1389, pc 1961..1961. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1196 .JUMPDEST]

/-- Instructions 1438..1395, pc 1832..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1197 .JUMPDEST,
   pushAt 1198 1 1,
   opAt 1199 .SHR,
   opAt 1200 (.Dup ⟨0, by decide⟩),
   pushAt 1201 2 1616,
   opAt 1202 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
