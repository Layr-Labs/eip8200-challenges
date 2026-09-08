import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1627..1682). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1627..1661, pc 2500..2634. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1607 .JUMPDEST,
   opAt 1608 (.Dup ⟨1, by decide⟩),
   opAt 1609 .MLOAD,
   opAt 1610 (.Dup ⟨3, by decide⟩),
   opAt 1611 .MLOAD,
   opAt 1612 (.Dup ⟨1, by decide⟩),
   opAt 1613 .ADD,
   opAt 1614 (.Swap ⟨0, by decide⟩),
   opAt 1615 (.Dup ⟨1, by decide⟩),
   opAt 1616 .LT,
   opAt 1617 (.Swap ⟨0, by decide⟩),
   opAt 1618 (.Dup ⟨5, by decide⟩),
   opAt 1619 .ADD,
   opAt 1620 (.Swap ⟨4, by decide⟩),
   opAt 1621 (.Dup ⟨5, by decide⟩),
   opAt 1622 .LT,
   opAt 1623 .OR,
   opAt 1624 (.Swap ⟨3, by decide⟩),
   opAt 1625 (.Dup ⟨1, by decide⟩),
   opAt 1626 .MSTORE,
   pushAt 1627 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1628 .ADD,
   opAt 1629 (.Swap ⟨0, by decide⟩),
   pushAt 1630 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1631 .ADD,
   opAt 1632 (.Swap ⟨0, by decide⟩),
   opAt 1633 (.Swap ⟨1, by decide⟩),
   pushAt 1634 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1635 .ADD,
   opAt 1636 (.Swap ⟨1, by decide⟩),
   pushAt 1637 2 8224,
   opAt 1638 (.Dup ⟨1, by decide⟩),
   opAt 1639 .GT,
   pushAt 1640 2 2468,
   opAt 1641 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2641. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1642 .POP,
   opAt 1643 .POP,
   opAt 1644 .POP,
   pushAt 1645 2 8224,
   opAt 1646 .MSTORE]

/-- Instructions 1667..1682, pc 2642..2665. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1647 .JUMPDEST,
   pushAt 1648 2 9440,
   opAt 1649 .MLOAD,
   pushAt 1650 2 9408,
   opAt 1651 .MLOAD,
   opAt 1652 (.Dup ⟨0, by decide⟩),
   pushAt 1653 2 7168,
   opAt 1654 .ADD,
   pushAt 1655 2 8256,
      opAt 1656 .POP,
   pushAt 1657 0 0,
   opAt 1658 (.Swap ⟨2, by decide⟩),
   opAt 1659 (.Swap ⟨0, by decide⟩),
   opAt 1660 (.Swap ⟨1, by decide⟩),
   opAt 1661 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
