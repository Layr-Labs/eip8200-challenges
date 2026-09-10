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
  [opAt 1247 .JUMPDEST,
   opAt 1248 .POP,
   opAt 1249 .POP,
   pushAt 1250 2 1755,
   pushAt 1251 2 2048,
   pushAt 1252 2 6144,
   pushAt 1253 2 1024,
   pushAt 1254 2 4465,
   opAt 1255 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1256 .JUMPDEST]

/-- Instructions 1265..1267, pc 1756..1760. The fixed-exponent candidate
redirects `BDONE` to its appended dispatcher; indices 1268..1271 are inert
padding and are not part of the executed block. -/
def blk1265 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1257 .JUMPDEST,
   pushAt 1258 2 3651,
   opAt 1259 .JUMP]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1264 .JUMPDEST,
   opAt 1265 (.Dup ⟨4, by decide⟩),
   opAt 1266 (.Dup ⟨1, by decide⟩),
   opAt 1267 .EQ,
   opAt 1268 .JUMPDEST,
   pushAt 1269 2 1850,
   opAt 1270 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1271 2 2555,
   opAt 1272 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1279 .JUMPDEST,
   pushAt 1280 2 1806,
   pushAt 1281 2 1024,
   pushAt 1282 2 1024,
   pushAt 1283 2 1024,
   pushAt 1284 2 4465,
   opAt 1285 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1286 .JUMPDEST,
   opAt 1287 (.Dup ⟨1, by decide⟩),
   opAt 1288 (.Dup ⟨1, by decide⟩),
   opAt 1289 .AND,
   opAt 1290 .ISZERO,
   pushAt 1291 2 1832,
   opAt 1292 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1293 2 1831,
   pushAt 1294 2 1024,
   pushAt 1295 2 2048,
   pushAt 1296 2 1024,
   pushAt 1297 2 4465,
   opAt 1298 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1299 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1300 .JUMPDEST,
   pushAt 1301 1 1,
   opAt 1302 .SHR,
   opAt 1303 (.Dup ⟨0, by decide⟩),
   pushAt 1304 2 1789,
   opAt 1305 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
