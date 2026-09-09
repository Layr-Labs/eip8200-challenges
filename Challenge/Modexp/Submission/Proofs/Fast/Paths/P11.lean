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
  [opAt 1562 .POP,
   opAt 1563 .POP,
   opAt 1564 (.Swap ⟨1, by decide⟩),
   opAt 1565 .POP,
   opAt 1566 .POP,
   opAt 1567 .JUMPDEST,
   opAt 1568 (.Dup ⟨0, by decide⟩),
   pushAt 1569 2 8224,
   opAt 1570 .MLOAD,
   opAt 1571 .ADD,
   opAt 1572 (.Dup ⟨0, by decide⟩),
   pushAt 1573 2 8256,
   opAt 1574 .MSTORE,
   opAt 1575 .LT,
   pushAt 1576 2 8192,
   opAt 1577 .MLOAD,
   opAt 1578 .ADD,
   pushAt 1579 2 8224,
   opAt 1580 .MSTORE,
   pushAt 1581 1 31, opAt 1582 .NOT,
   opAt 1583 .ADD,
   opAt 1584 (.Dup ⟨2, by decide⟩),
   opAt 1585 (.Dup ⟨1, by decide⟩),
   opAt 1586 .GT,
   pushAt 1587 2 1974,
   opAt 1588 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1589 .POP,
   opAt 1590 .POP,
   opAt 1591 .POP,
   pushAt 1592 2 2304,
   opAt 1593 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1594 .JUMPDEST,
   pushAt 1595 2 9344,
   opAt 1596 .MLOAD,
   opAt 1597 (.Dup ⟨0, by decide⟩),
   opAt 1598 (.Dup ⟨2, by decide⟩),
   opAt 1599 .ADD,
   pushAt 1600 1 32,
   opAt 1601 (.Swap ⟨0, by decide⟩),
   opAt 1602 .SUB,
   opAt 1603 (.Dup ⟨1, by decide⟩),
   opAt 1604 (.Dup ⟨4, by decide⟩),
   opAt 1605 .ADD,
   pushAt 1606 1 32,
   opAt 1607 (.Swap ⟨0, by decide⟩),
   opAt 1608 .SUB,
   opAt 1609 (.Swap ⟨2, by decide⟩),
   opAt 1610 .POP,
   opAt 1611 (.Swap ⟨2, by decide⟩),
   opAt 1612 .POP,
   opAt 1613 .POP,
   pushAt 1614 2 9440,
   opAt 1615 .MLOAD,
   pushAt 1616 0 0,
   opAt 1617 .JUMPDEST,
   opAt 1618 .JUMPDEST,
   opAt 1619 (.Swap ⟨2, by decide⟩),
   opAt 1620 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
