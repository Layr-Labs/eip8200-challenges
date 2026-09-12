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
  [opAt 1451 .POP,
   opAt 1452 .POP,
   opAt 1453 (.Swap ⟨1, by decide⟩),
   opAt 1454 .POP,
   opAt 1455 .POP,
   opAt 1456 (.Dup ⟨0, by decide⟩),
   pushAt 1457 2 8224,
   opAt 1458 .MLOAD,
   opAt 1459 .ADD,
   opAt 1460 (.Dup ⟨0, by decide⟩),
   pushAt 1461 2 8256,
   opAt 1462 .MSTORE,
   opAt 1463 .LT,
   pushAt 1464 2 8192,
   opAt 1465 .MLOAD,
   opAt 1466 .ADD,
   pushAt 1467 2 8224,
   opAt 1468 .MSTORE,
   pushAt 1469 1 31,
   opAt 1470 .NOT,
   opAt 1471 .ADD,
   opAt 1472 (.Dup ⟨2, by decide⟩),
   opAt 1473 (.Dup ⟨1, by decide⟩),
   opAt 1474 .GT,
   pushAt 1475 2 1796,
   opAt 1476 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1477 .POP,
   opAt 1478 .POP,
   opAt 1479 .POP,
   pushAt 1480 2 4804,
   opAt 1481 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1482 .JUMPDEST,
   pushAt 1483 2 9344,
   opAt 1484 .MLOAD,
   opAt 1485 (.Dup ⟨0, by decide⟩),
   opAt 1486 (.Dup ⟨2, by decide⟩),
   opAt 1487 .ADD,
   pushAt 1488 1 32,
   opAt 1489 (.Swap ⟨0, by decide⟩),
   opAt 1490 .SUB,
   opAt 1491 (.Dup ⟨1, by decide⟩),
   opAt 1492 (.Dup ⟨4, by decide⟩),
   opAt 1493 .ADD,
   pushAt 1494 1 32,
   opAt 1495 (.Swap ⟨0, by decide⟩),
   opAt 1496 .SUB,
   opAt 1497 (.Swap ⟨2, by decide⟩),
   opAt 1498 .POP,
   opAt 1499 (.Swap ⟨2, by decide⟩),
   opAt 1500 .POP,
   opAt 1501 .POP,
   pushAt 1502 2 9440,
   opAt 1503 .MLOAD,
   pushAt 1504 0 0,
   opAt 1505 (.Swap ⟨2, by decide⟩),
   opAt 1506 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
