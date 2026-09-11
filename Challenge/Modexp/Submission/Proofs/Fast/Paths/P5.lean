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
  [opAt 1176 .JUMPDEST,
   opAt 1177 .POP,
   opAt 1178 .POP,
   pushAt 1179 2 1616,
   pushAt 1180 2 512,
   pushAt 1181 2 1536,
   pushAt 1182 2 256,
   pushAt 1183 2 4053,
   opAt 1184 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1185 .JUMPDEST]

/-- Instructions 1265..1267, pc 1756..1760. The fixed-exponent candidate
redirects `BDONE` to its appended dispatcher; indices 1268..1271 are inert
padding and are not part of the executed block. -/
def blk1265 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1186 .JUMPDEST,
   pushAt 1187 2 3324,
   opAt 1188 .JUMP]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1189 .JUMPDEST,
   opAt 1190 (.Dup ⟨4, by decide⟩),
   opAt 1191 (.Dup ⟨1, by decide⟩),
   opAt 1192 .EQ,
   pushAt 1193 2 1695,
   opAt 1194 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1195 2 2262,
   opAt 1196 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1197 .JUMPDEST,
   pushAt 1198 2 1651,
   pushAt 1199 2 256,
   pushAt 1200 2 256,
   pushAt 1201 2 256,
   pushAt 1202 2 4053,
   opAt 1203 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1204 .JUMPDEST,
   opAt 1205 (.Dup ⟨1, by decide⟩),
   opAt 1206 (.Dup ⟨1, by decide⟩),
   opAt 1207 .AND,
   opAt 1208 .ISZERO,
   pushAt 1209 2 1677,
   opAt 1210 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1211 2 1676,
   pushAt 1212 2 256,
   pushAt 1213 2 512,
   pushAt 1214 2 256,
   pushAt 1215 2 4053,
   opAt 1216 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1217 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1218 .JUMPDEST,
   pushAt 1219 1 1,
   opAt 1220 .SHR,
   opAt 1221 (.Dup ⟨0, by decide⟩),
   pushAt 1222 2 1634,
   opAt 1223 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
