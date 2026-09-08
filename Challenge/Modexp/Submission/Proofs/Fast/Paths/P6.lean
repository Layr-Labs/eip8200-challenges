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
  [opAt 1306 .POP,
   opAt 1307 .POP,
   pushAt 1308 1 1,
   opAt 1309 .ADD,
   pushAt 1310 2 1739,
   opAt 1311 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1312 .JUMPDEST,
   opAt 1313 .POP,
   pushAt 1314 1 1,
   opAt 1315 (.Dup ⟨1, by decide⟩),
   pushAt 1316 2 3040,
   opAt 1317 .ADD,
   opAt 1318 .MSTORE,
   pushAt 1319 2 1845,
   pushAt 1320 2 1024,
   pushAt 1321 2 3072,
   pushAt 1322 2 1024,
   pushAt 1323 2 1908,
   opAt 1324 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1325 .JUMPDEST,
   opAt 1326 (.Dup ⟨4, by decide⟩),
   opAt 1327 (.Dup ⟨0, by decide⟩),
   opAt 1328 (.Dup ⟨2, by decide⟩),
   pushAt 1329 2 1024,
   opAt 1330 .ADD,
   opAt 1331 .SUB,
   opAt 1332 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1333 .JUMPDEST,
   opAt 1334 .POP,
   pushAt 1335 2 1185,
   opAt 1336 .JUMP]

/-- Instructions 1345..1350, pc 1892..1899. -/
def blk1345 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1337 .JUMPDEST,
   opAt 1338 .POP,
   opAt 1339 .POP,
   opAt 1340 .POP,
   pushAt 1341 2 1185,
   opAt 1342 .JUMP]

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1343 .JUMPDEST,
   opAt 1344 .POP,
   opAt 1345 .POP,
   opAt 1346 .POP,
   opAt 1347 .POP,
   opAt 1348 .POP,
   opAt 1349 .POP,
   pushAt 1350 2 1185,
   opAt 1351 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1352 .JUMPDEST,
   pushAt 1353 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1354 .JUMPDEST,
   pushAt 1355 2 1895,
   opAt 1356 (.Dup ⟨2, by decide⟩),
   opAt 1357 (.Dup ⟨0, by decide⟩),
   opAt 1358 (.Dup ⟨0, by decide⟩),
   pushAt 1359 2 2324,
   opAt 1360 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
