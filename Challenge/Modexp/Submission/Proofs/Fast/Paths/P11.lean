import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1751). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1719, pc 2304..2592. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1446 .POP,
   opAt 1447 .POP,
   opAt 1448 (.Swap ⟨1, by decide⟩),
   opAt 1449 .POP,
   opAt 1450 .POP,
   opAt 1451 (.Dup ⟨0, by decide⟩),
   pushAt 1452 2 2080,
   opAt 1453 .MLOAD,
   opAt 1454 .ADD,
   opAt 1455 (.Dup ⟨0, by decide⟩),
   pushAt 1456 2 2112,
   opAt 1457 .MSTORE,
   opAt 1458 .LT,
   pushAt 1459 2 2048,
   opAt 1460 .MLOAD,
   opAt 1461 .ADD,
   pushAt 1462 2 2080,
   opAt 1463 .MSTORE,
   pushAt 1464 1 31,
   opAt 1465 .NOT,
   opAt 1466 .ADD,
   opAt 1467 (.Dup ⟨2, by decide⟩),
   opAt 1468 (.Dup ⟨1, by decide⟩),
   opAt 1469 .GT,
   pushAt 1470 2 1786,
   opAt 1471 .JUMPI]

/-- Instructions 1672..1724, pc 2593..2344. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1472 .POP,
   opAt 1473 .POP,
   opAt 1474 .POP,
   pushAt 1475 2 4875,
   opAt 1476 .JUMP]

/-- Instructions 1600..1751, pc 2345..2377. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1477 .JUMPDEST,
   pushAt 1478 2 2688,
   opAt 1479 .MLOAD,
   opAt 1480 (.Dup ⟨0, by decide⟩),
   opAt 1481 (.Dup ⟨2, by decide⟩),
   opAt 1482 .ADD,
   pushAt 1483 1 32,
   opAt 1484 (.Swap ⟨0, by decide⟩),
   opAt 1485 .SUB,
   opAt 1486 (.Dup ⟨1, by decide⟩),
   opAt 1487 (.Dup ⟨4, by decide⟩),
   opAt 1488 .ADD,
   pushAt 1489 1 32,
   opAt 1490 (.Swap ⟨0, by decide⟩),
   opAt 1491 .SUB,
   opAt 1492 (.Swap ⟨2, by decide⟩),
   opAt 1493 .POP,
   opAt 1494 (.Swap ⟨2, by decide⟩),
   opAt 1495 .POP,
   opAt 1496 .POP,
   pushAt 1497 2 2784,
   opAt 1498 .MLOAD,
   pushAt 1499 0 0,
   opAt 1500 (.Swap ⟨2, by decide⟩),
   opAt 1501 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
