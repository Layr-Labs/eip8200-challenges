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
  [opAt 1560 .POP,
   opAt 1561 .POP,
   opAt 1562 (.Swap ⟨1, by decide⟩),
   opAt 1563 .POP,
   opAt 1564 .POP,
   opAt 1565 .JUMPDEST,
   opAt 1566 (.Dup ⟨0, by decide⟩),
   pushAt 1567 2 8224,
   opAt 1568 .MLOAD,
   opAt 1569 .ADD,
   opAt 1570 (.Dup ⟨0, by decide⟩),
   pushAt 1571 2 8256,
   opAt 1572 .MSTORE,
   opAt 1573 .LT,
   pushAt 1574 2 8192,
   opAt 1575 .MLOAD,
   opAt 1576 .ADD,
   pushAt 1577 2 8224,
   opAt 1578 .MSTORE,
   pushAt 1579 1 31, opAt 1580 .NOT,
   opAt 1581 .ADD,
   opAt 1582 (.Dup ⟨2, by decide⟩),
   opAt 1583 (.Dup ⟨1, by decide⟩),
   opAt 1584 .GT,
   pushAt 1585 2 1965,
   opAt 1586 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1587 .POP,
   opAt 1588 .POP,
   opAt 1589 .POP,
   pushAt 1590 2 2288,
   opAt 1591 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1592 .JUMPDEST,
   pushAt 1593 2 9344,
   opAt 1594 .MLOAD,
   opAt 1595 (.Dup ⟨0, by decide⟩),
   opAt 1596 (.Dup ⟨2, by decide⟩),
   opAt 1597 .ADD,
   pushAt 1598 1 32,
   opAt 1599 (.Swap ⟨0, by decide⟩),
   opAt 1600 .SUB,
   opAt 1601 (.Dup ⟨1, by decide⟩),
   opAt 1602 (.Dup ⟨4, by decide⟩),
   opAt 1603 .ADD,
   pushAt 1604 1 32,
   opAt 1605 (.Swap ⟨0, by decide⟩),
   opAt 1606 .SUB,
   opAt 1607 (.Swap ⟨2, by decide⟩),
   opAt 1608 .POP,
   opAt 1609 (.Swap ⟨2, by decide⟩),
   opAt 1610 .POP,
   opAt 1611 .POP,
   pushAt 1612 2 9440,
   opAt 1613 .MLOAD,
   pushAt 1614 0 0,
   opAt 1615 .JUMPDEST,
   opAt 1616 .JUMPDEST,
   opAt 1617 (.Swap ⟨2, by decide⟩),
   opAt 1618 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
