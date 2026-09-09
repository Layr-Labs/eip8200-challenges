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
  [opAt 1310 .POP,
   opAt 1311 .POP,
   pushAt 1312 1 1,
   opAt 1313 .ADD,
   pushAt 1314 2 1760,
   opAt 1315 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1316 .JUMPDEST,
   opAt 1317 .POP,
   pushAt 1318 1 1,
   opAt 1319 (.Dup ⟨1, by decide⟩),
   pushAt 1320 2 3040,
   opAt 1321 .ADD,
   opAt 1322 .MSTORE,
   pushAt 1323 2 1867,
   pushAt 1324 2 1024,
   pushAt 1325 2 3072,
   pushAt 1326 2 1024,
   pushAt 1327 2 4428,
   opAt 1328 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1329 .JUMPDEST,
   opAt 1330 (.Dup ⟨4, by decide⟩),
   opAt 1331 (.Dup ⟨0, by decide⟩),
   opAt 1332 (.Dup ⟨2, by decide⟩),
   pushAt 1333 2 1024,
   opAt 1334 .ADD,
   opAt 1335 .SUB,
   opAt 1336 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1337 .JUMPDEST,
   opAt 1338 .POP,
   pushAt 1339 2 1196,
   opAt 1340 .JUMP]

/-- Instructions 1345..1350, pc 1892..1899. -/
def blk1345 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1341 .JUMPDEST,
   opAt 1342 .POP,
   opAt 1343 .POP,
   opAt 1344 .POP,
   pushAt 1345 2 1196,
   opAt 1346 .JUMP]

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1347 .JUMPDEST,
   opAt 1348 .POP,
   opAt 1349 .POP,
   opAt 1350 .POP,
   opAt 1351 .POP,
   opAt 1352 .POP,
   opAt 1353 .POP,
   pushAt 1354 2 1196,
   opAt 1355 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1356 .JUMPDEST,
   pushAt 1357 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1358 .JUMPDEST,
   pushAt 1359 2 1917,
   opAt 1360 (.Dup ⟨2, by decide⟩),
   opAt 1361 (.Dup ⟨0, by decide⟩),
   opAt 1362 (.Dup ⟨0, by decide⟩),
   pushAt 1363 2 2203,
   opAt 1364 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
