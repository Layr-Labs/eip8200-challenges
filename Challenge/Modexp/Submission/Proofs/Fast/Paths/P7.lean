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
  [opAt 1369 .JUMPDEST,
   pushAt 1370 1 1,
   opAt 1371 (.Swap ⟨0, by decide⟩),
   opAt 1372 .SUB,
   opAt 1373 (.Dup ⟨0, by decide⟩),
   pushAt 1374 2 1915,
   opAt 1375 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1376 .POP,
   opAt 1377 .POP,
   opAt 1378 .JUMP]

/-- Instructions 1379..1405 plus the hoisted `TL` load, pc 1939..1974. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1379 .JUMPDEST,
   pushAt 1380 2 9440,
   opAt 1381 .MLOAD,
   opAt 1382 (.Swap ⟨3, by decide⟩),
   opAt 1383 (.Swap ⟨2, by decide⟩),
   opAt 1384 (.Swap ⟨1, by decide⟩),
   opAt 1385 (.Swap ⟨0, by decide⟩),
   pushAt 1386 2 9344,
   opAt 1387 .MLOAD,
   opAt 1388 (.Dup ⟨0, by decide⟩),
   pushAt 1389 1 64,
   opAt 1390 .ADD,
   opAt 1391 .CALLDATASIZE,
   pushAt 1392 2 8192,
   opAt 1393 .CALLDATACOPY,
   opAt 1394 (.Dup ⟨0, by decide⟩),
   opAt 1395 (.Dup ⟨3, by decide⟩),
   opAt 1396 .ADD,
   pushAt 1397 1 32,
   opAt 1398 (.Swap ⟨0, by decide⟩),
   opAt 1399 .SUB,
   pushAt 1400 1 32,
   opAt 1401 (.Dup ⟨4, by decide⟩),
   opAt 1402 .SUB,
   opAt 1403 (.Swap ⟨3, by decide⟩),
   opAt 1404 .POP,
   opAt 1405 (.Swap ⟨0, by decide⟩),
   opAt 1406 .POP,
   pushAt 1407 1 32,
   opAt 1408 (.Dup ⟨2, by decide⟩),
   opAt 1409 .SUB,
   opAt 1410 (.Swap ⟨1, by decide⟩),
   opAt 1411 .POP]

/-- Instructions 1425..1433, pc 2004..2014. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1425 .JUMPDEST,
   opAt 1426 (.Dup ⟨0, by decide⟩),
   opAt 1427 .MLOAD,
   pushAt 1428 0 0,
   opAt 1429 (.Dup ⟨7, by decide⟩),
   opAt 1430 (.Dup ⟨4, by decide⟩),
   pushAt 1431 2 9344,
   opAt 1432 .MLOAD,
   opAt 1433 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
