import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1756). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1724, pc 2309..2582. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1449 .POP,
   opAt 1450 .POP,
   opAt 1451 (.Swap ⟨1, by decide⟩),
   opAt 1452 .POP,
   opAt 1453 .POP,
   opAt 1454 (.Dup ⟨0, by decide⟩),
   pushAt 1455 2 4128,
   opAt 1456 .MLOAD,
   opAt 1457 .ADD,
   opAt 1458 (.Dup ⟨0, by decide⟩),
   pushAt 1459 2 4160,
   opAt 1460 .MSTORE,
   opAt 1461 .LT,
   pushAt 1462 2 4096,
   opAt 1463 .MLOAD,
   opAt 1464 .ADD,
   pushAt 1465 2 4128,
   opAt 1466 .MSTORE,
   pushAt 1467 1 31,
   opAt 1468 .NOT,
   opAt 1469 .ADD,
   opAt 1470 (.Dup ⟨2, by decide⟩),
   opAt 1471 (.Dup ⟨1, by decide⟩),
   opAt 1472 .GT,
   pushAt 1473 2 1791,
   opAt 1474 .JUMPI]

/-- Instructions 1677..1729, pc 2583..2350. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1475 .POP,
   opAt 1476 .POP,
   opAt 1477 .POP,
   pushAt 1478 2 4874,
   opAt 1479 .JUMP]

/-- Instructions 1600..1756, pc 2351..2383. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1480 .JUMPDEST,
   pushAt 1481 2 5248,
   opAt 1482 .MLOAD,
   opAt 1483 (.Dup ⟨0, by decide⟩),
   opAt 1484 (.Dup ⟨2, by decide⟩),
   opAt 1485 .ADD,
   pushAt 1486 1 32,
   opAt 1487 (.Swap ⟨0, by decide⟩),
   opAt 1488 .SUB,
   opAt 1489 (.Dup ⟨1, by decide⟩),
   opAt 1490 (.Dup ⟨4, by decide⟩),
   opAt 1491 .ADD,
   pushAt 1492 1 32,
   opAt 1493 (.Swap ⟨0, by decide⟩),
   opAt 1494 .SUB,
   opAt 1495 (.Swap ⟨2, by decide⟩),
   opAt 1496 .POP,
   opAt 1497 (.Swap ⟨2, by decide⟩),
   opAt 1498 .POP,
   opAt 1499 .POP,
   pushAt 1500 2 5344,
   opAt 1501 .MLOAD,
   pushAt 1502 0 0,
   opAt 1503 (.Swap ⟨2, by decide⟩),
   opAt 1504 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
