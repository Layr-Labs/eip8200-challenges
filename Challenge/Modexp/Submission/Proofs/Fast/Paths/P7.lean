import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1369..1420). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1369..1375, pc 1926..1935. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1321 .JUMPDEST,
   pushAt 1322 1 1,
   opAt 1323 (.Swap ⟨0, by decide⟩),
   opAt 1324 .SUB,
   opAt 1325 (.Dup ⟨0, by decide⟩),
   pushAt 1326 2 1841,
   opAt 1327 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1328 .POP,
   opAt 1329 .POP,
   opAt 1330 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1331 .JUMPDEST,
   pushAt 1332 2 9344,
   opAt 1333 .MLOAD,
   opAt 1334 (.Dup ⟨0, by decide⟩),
   pushAt 1335 1 64,
   opAt 1336 .ADD,
   opAt 1337 .CALLDATASIZE,
   pushAt 1338 2 8192,
   opAt 1339 .CALLDATACOPY,
   opAt 1340 (.Dup ⟨0, by decide⟩),
   opAt 1341 (.Dup ⟨3, by decide⟩),
   opAt 1342 .ADD,
   pushAt 1343 1 32,
   opAt 1344 (.Swap ⟨0, by decide⟩),
   opAt 1345 .SUB,
   pushAt 1346 1 32,
   opAt 1347 (.Dup ⟨4, by decide⟩),
   opAt 1348 .SUB,
   opAt 1349 (.Swap ⟨3, by decide⟩),
   opAt 1350 .POP,
   opAt 1351 (.Swap ⟨0, by decide⟩),
   opAt 1352 .POP,
   pushAt 1353 1 32,
   opAt 1354 (.Dup ⟨2, by decide⟩),
   opAt 1355 .SUB,
   opAt 1356 (.Swap ⟨1, by decide⟩),
   opAt 1357 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1358 .JUMPDEST,
   opAt 1359 (.Dup ⟨0, by decide⟩),
   opAt 1360 .MLOAD,
   pushAt 1361 0 0,
   pushAt 1362 2 9440,
   opAt 1363 .MLOAD,
   opAt 1364 (.Dup ⟨4, by decide⟩),
   pushAt 1365 2 9344,
   opAt 1366 .MLOAD,
   opAt 1367 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
