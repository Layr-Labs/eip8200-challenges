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
  [opAt 1238 .JUMPDEST,
   opAt 1239 .POP,
   opAt 1240 .POP,
   pushAt 1241 2 1737,
   pushAt 1242 2 2048,
   pushAt 1243 2 6144,
   pushAt 1244 2 1024,
   pushAt 1245 2 4428,
   opAt 1246 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1247 .JUMPDEST]

/-- Instructions 1265..1267, pc 1756..1760. The fixed-exponent candidate
redirects `BDONE` to its appended dispatcher; indices 1268..1271 are inert
padding and are not part of the executed block. -/
def blk1265 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1248 .JUMPDEST,
   pushAt 1249 2 3618,
   opAt 1250 .JUMP]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1255 .JUMPDEST,
   opAt 1256 (.Dup ⟨4, by decide⟩),
   opAt 1257 (.Dup ⟨1, by decide⟩),
   opAt 1258 .EQ,
   pushAt 1259 2 1831,
   opAt 1260 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1261 2 2526,
   opAt 1262 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1269 .JUMPDEST,
   pushAt 1270 2 1787,
   pushAt 1271 2 1024,
   pushAt 1272 2 1024,
   pushAt 1273 2 1024,
   pushAt 1274 2 4428,
   opAt 1275 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1276 .JUMPDEST,
   opAt 1277 (.Dup ⟨1, by decide⟩),
   opAt 1278 (.Dup ⟨1, by decide⟩),
   opAt 1279 .AND,
   opAt 1280 .ISZERO,
   pushAt 1281 2 1813,
   opAt 1282 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1283 2 1812,
   pushAt 1284 2 1024,
   pushAt 1285 2 2048,
   pushAt 1286 2 1024,
   pushAt 1287 2 4428,
   opAt 1288 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1289 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1290 .JUMPDEST,
   pushAt 1291 1 1,
   opAt 1292 .SHR,
   opAt 1293 (.Dup ⟨0, by decide⟩),
   pushAt 1294 2 1770,
   opAt 1295 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
