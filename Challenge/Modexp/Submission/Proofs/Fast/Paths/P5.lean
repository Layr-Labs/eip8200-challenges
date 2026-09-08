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
   pushAt 1250 2 1747,
   pushAt 1251 2 2048,
   pushAt 1252 2 6144,
   pushAt 1253 2 1024,
   pushAt 1254 2 4176,
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
   pushAt 1258 2 3374,
   opAt 1259 .JUMP]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1264 .JUMPDEST,
   opAt 1265 (.Dup ⟨4, by decide⟩),
   opAt 1266 (.Dup ⟨1, by decide⟩),
   opAt 1267 .EQ,
      pushAt 1268 2 1841,
   opAt 1269 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1270 2 2536,
   opAt 1271 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1278 .JUMPDEST,
   pushAt 1279 2 1797,
   pushAt 1280 2 1024,
   pushAt 1281 2 1024,
   pushAt 1282 2 1024,
   pushAt 1283 2 4176,
   opAt 1284 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1285 .JUMPDEST,
   opAt 1286 (.Dup ⟨1, by decide⟩),
   opAt 1287 (.Dup ⟨1, by decide⟩),
   opAt 1288 .AND,
   opAt 1289 .ISZERO,
   pushAt 1290 2 1823,
   opAt 1291 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1292 2 1822,
   pushAt 1293 2 1024,
   pushAt 1294 2 2048,
   pushAt 1295 2 1024,
   pushAt 1296 2 4176,
   opAt 1297 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1298 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1299 .JUMPDEST,
   pushAt 1300 1 1,
   opAt 1301 .SHR,
   opAt 1302 (.Dup ⟨0, by decide⟩),
   pushAt 1303 2 1780,
   opAt 1304 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
