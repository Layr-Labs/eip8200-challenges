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
  [opAt 1558 .POP,
   opAt 1559 .POP,
   opAt 1560 (.Swap ⟨1, by decide⟩),
   opAt 1561 .POP,
   opAt 1562 .POP,
   opAt 1563 .JUMPDEST,
   opAt 1564 (.Dup ⟨0, by decide⟩),
   pushAt 1565 2 8224,
   opAt 1566 .MLOAD,
   opAt 1567 .ADD,
   opAt 1568 (.Dup ⟨0, by decide⟩),
   pushAt 1569 2 8256,
   opAt 1570 .MSTORE,
   opAt 1571 .LT,
   pushAt 1572 2 8192,
   opAt 1573 .MLOAD,
   opAt 1574 .ADD,
   pushAt 1575 2 8224,
   opAt 1576 .MSTORE,
   pushAt 1577 1 31, opAt 1578 .NOT,
   opAt 1579 .ADD,
   opAt 1580 (.Dup ⟨2, by decide⟩),
   opAt 1581 (.Dup ⟨1, by decide⟩),
   opAt 1582 .GT,
   pushAt 1583 2 1974,
   opAt 1584 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1585 .POP,
   opAt 1586 .POP,
   opAt 1587 .POP,
   pushAt 1588 2 2304,
   opAt 1589 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1590 .JUMPDEST,
   pushAt 1591 2 9344,
   opAt 1592 .MLOAD,
   opAt 1593 (.Dup ⟨0, by decide⟩),
   opAt 1594 (.Dup ⟨2, by decide⟩),
   opAt 1595 .ADD,
   pushAt 1596 1 32,
   opAt 1597 (.Swap ⟨0, by decide⟩),
   opAt 1598 .SUB,
   opAt 1599 (.Dup ⟨1, by decide⟩),
   opAt 1600 (.Dup ⟨4, by decide⟩),
   opAt 1601 .ADD,
   pushAt 1602 1 32,
   opAt 1603 (.Swap ⟨0, by decide⟩),
   opAt 1604 .SUB,
   opAt 1605 (.Swap ⟨2, by decide⟩),
   opAt 1606 .POP,
   opAt 1607 (.Swap ⟨2, by decide⟩),
   opAt 1608 .POP,
   opAt 1609 .POP,
   pushAt 1610 2 9440,
   opAt 1611 .MLOAD,
   pushAt 1612 0 0,
   opAt 1613 .JUMPDEST,
   opAt 1614 .JUMPDEST,
   opAt 1615 (.Swap ⟨2, by decide⟩),
   opAt 1616 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
