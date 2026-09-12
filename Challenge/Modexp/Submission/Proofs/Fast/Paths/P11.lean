import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1626). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1594, pc 2179..2459. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1452 .POP,
   opAt 1453 .POP,
   opAt 1454 (.Swap ⟨1, by decide⟩),
   opAt 1455 .POP,
   opAt 1456 .POP,
   opAt 1457 (.Dup ⟨0, by decide⟩),
   pushAt 1458 2 4128,
   opAt 1459 .MLOAD,
   opAt 1460 .ADD,
   opAt 1461 (.Dup ⟨0, by decide⟩),
   pushAt 1462 2 4160,
   opAt 1463 .MSTORE,
   opAt 1464 .LT,
   pushAt 1465 2 4096,
   opAt 1466 .MLOAD,
   opAt 1467 .ADD,
   pushAt 1468 2 4128,
   opAt 1469 .MSTORE,
   pushAt 1470 1 31,
   opAt 1471 .NOT,
   opAt 1472 .ADD,
   opAt 1473 (.Dup ⟨2, by decide⟩),
   opAt 1474 (.Dup ⟨1, by decide⟩),
   opAt 1475 .GT,
   pushAt 1476 2 1796,
   opAt 1477 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1478 .POP,
   opAt 1479 .POP,
   opAt 1480 .POP,
   pushAt 1481 2 4804,
   opAt 1482 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1483 .JUMPDEST,
   pushAt 1484 2 5248,
   opAt 1485 .MLOAD,
   opAt 1486 (.Dup ⟨0, by decide⟩),
   opAt 1487 (.Dup ⟨2, by decide⟩),
   opAt 1488 .ADD,
   pushAt 1489 1 32,
   opAt 1490 (.Swap ⟨0, by decide⟩),
   opAt 1491 .SUB,
   opAt 1492 (.Dup ⟨1, by decide⟩),
   opAt 1493 (.Dup ⟨4, by decide⟩),
   opAt 1494 .ADD,
   pushAt 1495 1 32,
   opAt 1496 (.Swap ⟨0, by decide⟩),
   opAt 1497 .SUB,
   opAt 1498 (.Swap ⟨2, by decide⟩),
   opAt 1499 .POP,
   opAt 1500 (.Swap ⟨2, by decide⟩),
   opAt 1501 .POP,
   opAt 1502 .POP,
   pushAt 1503 2 5344,
   opAt 1504 .MLOAD,
   pushAt 1505 0 0,
   opAt 1506 (.Swap ⟨2, by decide⟩),
   opAt 1507 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
