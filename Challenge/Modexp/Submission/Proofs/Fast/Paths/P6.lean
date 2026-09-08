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
  [opAt 1307 .POP,
   opAt 1308 .POP,
   pushAt 1309 1 1,
   opAt 1310 .ADD,
   pushAt 1311 2 1746,
   opAt 1312 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1313 .JUMPDEST,
   opAt 1314 .POP,
   pushAt 1315 1 1,
   opAt 1316 (.Dup ⟨1, by decide⟩),
   pushAt 1317 2 3040,
   opAt 1318 .ADD,
   opAt 1319 .MSTORE,
   pushAt 1320 2 1852,
   pushAt 1321 2 1024,
   pushAt 1322 2 3072,
   pushAt 1323 2 1024,
   pushAt 1324 2 4751,
   opAt 1325 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1326 .JUMPDEST,
   opAt 1327 (.Dup ⟨4, by decide⟩),
   opAt 1328 (.Dup ⟨0, by decide⟩),
   opAt 1329 (.Dup ⟨2, by decide⟩),
   pushAt 1330 2 1024,
   opAt 1331 .ADD,
   opAt 1332 .SUB,
   opAt 1333 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1334 .JUMPDEST,
   opAt 1335 .POP,
   pushAt 1336 2 1192,
   opAt 1337 .JUMP]

/-- Instructions 1345..1350, pc 1892..1899. -/
def blk1345 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1338 .JUMPDEST,
   opAt 1339 .POP,
   opAt 1340 .POP,
   opAt 1341 .POP,
   pushAt 1342 2 1192,
   opAt 1343 .JUMP]

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1344 .JUMPDEST,
   opAt 1345 .POP,
   opAt 1346 .POP,
   opAt 1347 .POP,
   opAt 1348 .POP,
   opAt 1349 .POP,
   opAt 1350 .POP,
   pushAt 1351 2 1192,
   opAt 1352 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1353 .JUMPDEST,
   pushAt 1354 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1355 .JUMPDEST,
   pushAt 1356 2 1902,
   opAt 1357 (.Dup ⟨2, by decide⟩),
   opAt 1358 (.Dup ⟨0, by decide⟩),
   opAt 1359 (.Dup ⟨0, by decide⟩),
   pushAt 1360 2 2437,
   opAt 1361 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
