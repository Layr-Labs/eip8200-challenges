import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1683..1741). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1683..1723, pc 2333..2473. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1578 .JUMPDEST,
   opAt 1579 (.Dup ⟨0, by decide⟩),
   opAt 1580 .MLOAD,
   opAt 1581 (.Dup ⟨2, by decide⟩),
   opAt 1582 .MLOAD,
   opAt 1583 (.Dup ⟨1, by decide⟩),
   opAt 1584 (.Dup ⟨1, by decide⟩),
   opAt 1585 .GT,
   opAt 1586 (.Swap ⟨1, by decide⟩),
   opAt 1587 .SUB,
   opAt 1588 (.Dup ⟨5, by decide⟩),
   opAt 1589 (.Dup ⟨1, by decide⟩),
   opAt 1590 .SUB,
   opAt 1591 (.Swap ⟨0, by decide⟩),
   opAt 1592 (.Dup ⟨6, by decide⟩),
   opAt 1593 .GT,
   opAt 1594 (.Swap ⟨0, by decide⟩),
   opAt 1595 (.Swap ⟨1, by decide⟩),
   opAt 1596 .OR,
   opAt 1597 (.Swap ⟨4, by decide⟩),
   opAt 1598 .POP,
   opAt 1599 (.Dup ⟨3, by decide⟩),
   opAt 1600 .MSTORE,
   pushAt 1601 1 31,
   opAt 1602 .NOT,
   opAt 1603 .ADD,
   opAt 1604 (.Swap ⟨0, by decide⟩),
   pushAt 1605 1 31,
   opAt 1606 .NOT,
   opAt 1607 .ADD,
   opAt 1608 (.Swap ⟨0, by decide⟩),
   opAt 1609 (.Swap ⟨1, by decide⟩),
   pushAt 1610 1 31,
   opAt 1611 .NOT,
   opAt 1612 .ADD,
   opAt 1613 (.Swap ⟨1, by decide⟩),
   pushAt 1614 2 8224,
   opAt 1615 (.Dup ⟨1, by decide⟩),
   opAt 1616 .GT,
   pushAt 1617 2 2144,
   opAt 1618 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1619 .POP,
   opAt 1620 .POP,
   opAt 1621 .POP,
   opAt 1622 .ISZERO,
   pushAt 1623 2 8224,
   opAt 1624 .MLOAD,
   opAt 1625 .OR,
   pushAt 1626 2 1087,
   opAt 1627 .NOT,
   opAt 1628 .MUL,
   pushAt 1629 2 8256,
   opAt 1630 .ADD,
   pushAt 1631 2 9344,
   opAt 1632 .MLOAD,
   opAt 1633 (.Swap ⟨1, by decide⟩),
   opAt 1634 .MCOPY,
   opAt 1635 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
