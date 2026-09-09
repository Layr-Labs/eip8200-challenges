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
  [opAt 1251 .JUMPDEST,
   opAt 1252 .POP,
   opAt 1253 .POP,
   pushAt 1254 2 1755,
   pushAt 1255 2 2048,
   pushAt 1256 2 6144,
   pushAt 1257 2 1024,
   pushAt 1258 2 4458,
   opAt 1259 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1260 .JUMPDEST]

/-- Instructions 1265..1267, pc 1756..1760. The fixed-exponent candidate
redirects `BDONE` to its appended dispatcher; indices 1268..1271 are inert
padding and are not part of the executed block. -/
def blk1265 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1261 .JUMPDEST,
   pushAt 1262 2 3651,
   opAt 1263 .JUMP]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1268 .JUMPDEST,
   opAt 1269 (.Dup ⟨4, by decide⟩),
   opAt 1270 (.Dup ⟨1, by decide⟩),
   opAt 1271 .EQ,
   opAt 1272 .JUMPDEST,
   pushAt 1273 2 1850,
   opAt 1274 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1275 2 2555,
   opAt 1276 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1283 .JUMPDEST,
   pushAt 1284 2 1806,
   pushAt 1285 2 1024,
   pushAt 1286 2 1024,
   pushAt 1287 2 1024,
   pushAt 1288 2 4458,
   opAt 1289 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1290 .JUMPDEST,
   opAt 1291 (.Dup ⟨1, by decide⟩),
   opAt 1292 (.Dup ⟨1, by decide⟩),
   opAt 1293 .AND,
   opAt 1294 .ISZERO,
   pushAt 1295 2 1832,
   opAt 1296 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1297 2 1831,
   pushAt 1298 2 1024,
   pushAt 1299 2 2048,
   pushAt 1300 2 1024,
   pushAt 1301 2 4458,
   opAt 1302 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1303 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1304 .JUMPDEST,
   pushAt 1305 1 1,
   opAt 1306 .SHR,
   opAt 1307 (.Dup ⟨0, by decide⟩),
   pushAt 1308 2 1789,
   opAt 1309 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
