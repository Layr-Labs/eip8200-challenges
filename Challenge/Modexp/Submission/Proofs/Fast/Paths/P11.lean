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
  [opAt 1518 .POP,
   opAt 1519 .POP,
   opAt 1520 (.Swap ⟨1, by decide⟩),
   opAt 1521 .POP,
   opAt 1522 .POP,
   opAt 1523 (.Dup ⟨0, by decide⟩),
   pushAt 1524 2 8224,
   opAt 1525 .MLOAD,
   opAt 1526 .ADD,
   opAt 1527 (.Dup ⟨0, by decide⟩),
   pushAt 1528 2 8256,
   opAt 1529 .MSTORE,
   opAt 1530 .LT,
   pushAt 1531 2 8192,
   opAt 1532 .MLOAD,
   opAt 1533 .ADD,
   pushAt 1534 2 8224,
   opAt 1535 .MSTORE,
   pushAt 1536 1 31,
   opAt 1537 .NOT,
   opAt 1538 .ADD,
   opAt 1539 (.Dup ⟨2, by decide⟩),
   opAt 1540 (.Dup ⟨1, by decide⟩),
   opAt 1541 .GT,
   pushAt 1542 2 1900,
   opAt 1543 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1544 .POP,
   opAt 1545 .POP,
   opAt 1546 .POP,
   pushAt 1547 2 2220,
   opAt 1548 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1549 .JUMPDEST,
   pushAt 1550 2 9344,
   opAt 1551 .MLOAD,
   opAt 1552 (.Dup ⟨0, by decide⟩),
   opAt 1553 (.Dup ⟨2, by decide⟩),
   opAt 1554 .ADD,
   pushAt 1555 1 32,
   opAt 1556 (.Swap ⟨0, by decide⟩),
   opAt 1557 .SUB,
   opAt 1558 (.Dup ⟨1, by decide⟩),
   opAt 1559 (.Dup ⟨4, by decide⟩),
   opAt 1560 .ADD,
   pushAt 1561 1 32,
   opAt 1562 (.Swap ⟨0, by decide⟩),
   opAt 1563 .SUB,
   opAt 1564 (.Swap ⟨2, by decide⟩),
   opAt 1565 .POP,
   opAt 1566 (.Swap ⟨2, by decide⟩),
   opAt 1567 .POP,
   opAt 1568 .POP,
   pushAt 1569 2 9440,
   opAt 1570 .MLOAD,
   pushAt 1571 0 0,
   opAt 1572 (.Swap ⟨2, by decide⟩),
   opAt 1573 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
