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
  [opAt 1351 .JUMPDEST,
   pushAt 1352 1 1,
   opAt 1353 (.Swap ⟨0, by decide⟩),
   opAt 1354 .SUB,
   opAt 1355 (.Dup ⟨0, by decide⟩),
   pushAt 1356 2 1896,
   opAt 1357 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1358 .POP,
   opAt 1359 .POP,
   opAt 1360 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1361 .JUMPDEST,
   pushAt 1362 2 9344,
   opAt 1363 .MLOAD,
   opAt 1364 (.Dup ⟨0, by decide⟩),
   pushAt 1365 1 64,
   opAt 1366 .ADD,
   opAt 1367 .CALLDATASIZE,
   pushAt 1368 2 8192,
   opAt 1369 .CALLDATACOPY,
   opAt 1370 (.Dup ⟨0, by decide⟩),
   opAt 1371 (.Dup ⟨3, by decide⟩),
   opAt 1372 .ADD,
   pushAt 1373 1 32,
   opAt 1374 (.Swap ⟨0, by decide⟩),
   opAt 1375 .SUB,
   pushAt 1376 1 32,
   opAt 1377 (.Dup ⟨4, by decide⟩),
   opAt 1378 .SUB,
   opAt 1379 (.Swap ⟨3, by decide⟩),
   opAt 1380 .POP,
   opAt 1381 (.Swap ⟨0, by decide⟩),
   opAt 1382 .POP,
   pushAt 1383 1 32,
   opAt 1384 (.Dup ⟨2, by decide⟩),
   opAt 1385 .SUB,
   opAt 1386 (.Swap ⟨1, by decide⟩),
   opAt 1387 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1388 .JUMPDEST,
   opAt 1389 (.Dup ⟨0, by decide⟩),
   opAt 1390 .MLOAD,
   pushAt 1391 0 0,
   pushAt 1392 4 9440,
   opAt 1393 .MLOAD,
   opAt 1394 (.Dup ⟨4, by decide⟩),
   pushAt 1395 7 9344,
   opAt 1396 .MLOAD,
   opAt 1397 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
