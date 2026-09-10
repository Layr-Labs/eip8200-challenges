import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 6 (instructions 1314..1368). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1314..1319, pc 1841..1849. -/
def blk1314 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1266 .POP,
   opAt 1267 .POP,
   pushAt 1268 1 1,
   opAt 1269 .ADD,
   pushAt 1270 2 1703,
   opAt 1271 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1272 .JUMPDEST,
   opAt 1273 .POP,
   pushAt 1274 1 1,
   opAt 1275 (.Dup ⟨1, by decide⟩),
   pushAt 1276 2 3040,
   opAt 1277 .ADD,
   opAt 1278 .MSTORE,
   pushAt 1279 2 1802,
   pushAt 1280 2 1024,
   pushAt 1281 2 3072,
   pushAt 1282 2 1024,
   pushAt 1283 2 4137,
   opAt 1284 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1285 .JUMPDEST,
   opAt 1286 (.Dup ⟨4, by decide⟩),
   opAt 1287 (.Dup ⟨0, by decide⟩),
   opAt 1288 (.Dup ⟨2, by decide⟩),
   pushAt 1289 2 1024,
   opAt 1290 .ADD,
   opAt 1291 .SUB,
   opAt 1292 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1293 .JUMPDEST,
   opAt 1294 .POP,
   pushAt 1295 2 1196,
   opAt 1296 .JUMP]

/-- Instructions 1345..1350, pc 1892..1899. -/
def blk1345 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1297 .JUMPDEST,
   opAt 1298 .POP,
   opAt 1299 .POP,
   opAt 1300 .POP,
   pushAt 1301 2 1196,
   opAt 1302 .JUMP]

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1303 .JUMPDEST,
   opAt 1304 .POP,
   opAt 1305 .POP,
   opAt 1306 .POP,
   opAt 1307 .POP,
   opAt 1308 .POP,
   opAt 1309 .POP,
   pushAt 1310 2 1196,
   opAt 1311 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1312 .JUMPDEST,
   pushAt 1313 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1314 .JUMPDEST,
   pushAt 1315 2 1852,
   opAt 1316 (.Dup ⟨2, by decide⟩),
   opAt 1317 (.Dup ⟨0, by decide⟩),
   opAt 1318 (.Dup ⟨0, by decide⟩),
   pushAt 1319 2 2137,
   opAt 1320 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
