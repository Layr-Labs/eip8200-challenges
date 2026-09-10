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
  [opAt 1308 .POP,
   opAt 1309 .POP,
   pushAt 1310 1 1,
   opAt 1311 .ADD,
   pushAt 1312 2 1760,
   opAt 1313 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1314 .JUMPDEST,
   opAt 1315 .POP,
   pushAt 1316 1 1,
   opAt 1317 (.Dup ⟨1, by decide⟩),
   pushAt 1318 2 3040,
   opAt 1319 .ADD,
   opAt 1320 .MSTORE,
   pushAt 1321 2 1867,
   pushAt 1322 2 1024,
   pushAt 1323 2 3072,
   pushAt 1324 2 1024,
   pushAt 1325 2 4428,
   opAt 1326 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1327 .JUMPDEST,
   opAt 1328 (.Dup ⟨4, by decide⟩),
   opAt 1329 (.Dup ⟨0, by decide⟩),
   opAt 1330 (.Dup ⟨2, by decide⟩),
   pushAt 1331 2 1024,
   opAt 1332 .ADD,
   opAt 1333 .SUB,
   opAt 1334 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1335 .JUMPDEST,
   opAt 1336 .POP,
   pushAt 1337 2 1196,
   opAt 1338 .JUMP]

/-- Instructions 1345..1350, pc 1892..1899. -/
def blk1345 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1339 .JUMPDEST,
   opAt 1340 .POP,
   opAt 1341 .POP,
   opAt 1342 .POP,
   pushAt 1343 2 1196,
   opAt 1344 .JUMP]

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1345 .JUMPDEST,
   opAt 1346 .POP,
   opAt 1347 .POP,
   opAt 1348 .POP,
   opAt 1349 .POP,
   opAt 1350 .POP,
   opAt 1351 .POP,
   pushAt 1352 2 1196,
   opAt 1353 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1354 .JUMPDEST,
   pushAt 1355 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1356 .JUMPDEST,
   pushAt 1357 2 1917,
   opAt 1358 (.Dup ⟨2, by decide⟩),
   opAt 1359 (.Dup ⟨0, by decide⟩),
   opAt 1360 (.Dup ⟨0, by decide⟩),
   pushAt 1361 2 2203,
   opAt 1362 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
