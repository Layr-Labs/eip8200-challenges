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
  [opAt 1249 .JUMPDEST,
   opAt 1250 .POP,
   opAt 1251 .POP,
   pushAt 1252 2 1746,
   pushAt 1253 2 2048,
   pushAt 1254 2 6144,
   pushAt 1255 2 1024,
   pushAt 1256 2 4424,
   opAt 1257 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1258 .JUMPDEST]

/-- Instructions 1265..1267, pc 1756..1760. The fixed-exponent candidate
redirects `BDONE` to its appended dispatcher; indices 1268..1271 are inert
padding and are not part of the executed block. -/
def blk1265 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1259 .JUMPDEST,
   pushAt 1260 2 3615,
   opAt 1261 .JUMP]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1266 .JUMPDEST,
   opAt 1267 (.Dup ⟨4, by decide⟩),
   opAt 1268 (.Dup ⟨1, by decide⟩),
   opAt 1269 .EQ,
   opAt 1270 .JUMPDEST,
   pushAt 1271 2 1841,
   opAt 1272 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1273 2 2535,
   opAt 1274 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1281 .JUMPDEST,
   pushAt 1282 2 1797,
   pushAt 1283 2 1024,
   pushAt 1284 2 1024,
   pushAt 1285 2 1024,
   pushAt 1286 2 4424,
   opAt 1287 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1288 .JUMPDEST,
   opAt 1289 (.Dup ⟨1, by decide⟩),
   opAt 1290 (.Dup ⟨1, by decide⟩),
   opAt 1291 .AND,
   opAt 1292 .ISZERO,
   pushAt 1293 2 1823,
   opAt 1294 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1295 2 1822,
   pushAt 1296 2 1024,
   pushAt 1297 2 2048,
   pushAt 1298 2 1024,
   pushAt 1299 2 4424,
   opAt 1300 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1301 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1302 .JUMPDEST,
   pushAt 1303 1 1,
   opAt 1304 .SHR,
   opAt 1305 (.Dup ⟨0, by decide⟩),
   pushAt 1306 2 1780,
   opAt 1307 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
