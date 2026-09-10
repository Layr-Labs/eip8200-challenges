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
  [opAt 1566 .POP,
   opAt 1567 .POP,
   opAt 1568 (.Swap ⟨1, by decide⟩),
   opAt 1569 .POP,
   opAt 1570 .POP,
   opAt 1571 .JUMPDEST,
   opAt 1572 (.Dup ⟨0, by decide⟩),
   pushAt 1573 2 8224,
   opAt 1574 .MLOAD,
   opAt 1575 .ADD,
   opAt 1576 (.Dup ⟨0, by decide⟩),
   pushAt 1577 2 8256,
   opAt 1578 .MSTORE,
   opAt 1579 .LT,
   pushAt 1580 2 8192,
   opAt 1581 .MLOAD,
   opAt 1582 .ADD,
   pushAt 1583 2 8224,
   opAt 1584 .MSTORE,
   pushAt 1585 1 31, opAt 1586 .NOT,
   opAt 1587 .ADD,
   opAt 1588 (.Dup ⟨2, by decide⟩),
   opAt 1589 (.Dup ⟨1, by decide⟩),
   opAt 1590 .GT,
   pushAt 1591 2 1951,
   opAt 1592 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1593 .POP,
   opAt 1594 .POP,
   opAt 1595 .POP,
   pushAt 1596 2 2274,
   opAt 1597 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1598 .JUMPDEST,
   pushAt 1599 2 9344,
   opAt 1600 .MLOAD,
   opAt 1601 (.Dup ⟨0, by decide⟩),
   opAt 1602 (.Dup ⟨2, by decide⟩),
   opAt 1603 .ADD,
   pushAt 1604 1 32,
   opAt 1605 (.Swap ⟨0, by decide⟩),
   opAt 1606 .SUB,
   opAt 1607 (.Dup ⟨1, by decide⟩),
   opAt 1608 (.Dup ⟨4, by decide⟩),
   opAt 1609 .ADD,
   pushAt 1610 1 32,
   opAt 1611 (.Swap ⟨0, by decide⟩),
   opAt 1612 .SUB,
   opAt 1613 (.Swap ⟨2, by decide⟩),
   opAt 1614 .POP,
   opAt 1615 (.Swap ⟨2, by decide⟩),
   opAt 1616 .POP,
   opAt 1617 .POP,
   pushAt 1618 2 9440,
   opAt 1619 .MLOAD,
   pushAt 1620 0 0,
   opAt 1621 .JUMPDEST,
   opAt 1622 .JUMPDEST,
   opAt 1623 (.Swap ⟨2, by decide⟩),
   opAt 1624 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
