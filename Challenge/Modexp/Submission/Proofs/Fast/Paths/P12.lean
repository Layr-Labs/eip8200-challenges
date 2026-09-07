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
  [opAt 1622 .JUMPDEST,
   opAt 1623 (.Dup ⟨1, by decide⟩),
   opAt 1624 .MLOAD,
   opAt 1625 (.Dup ⟨3, by decide⟩),
   opAt 1626 .MLOAD,
   opAt 1627 (.Dup ⟨1, by decide⟩),
   opAt 1628 .ADD,
   opAt 1629 (.Swap ⟨0, by decide⟩),
   opAt 1630 (.Dup ⟨1, by decide⟩),
   opAt 1631 .LT,
   opAt 1632 (.Swap ⟨0, by decide⟩),
   opAt 1633 (.Dup ⟨5, by decide⟩),
   opAt 1634 .ADD,
   opAt 1635 (.Swap ⟨4, by decide⟩),
   opAt 1636 (.Dup ⟨5, by decide⟩),
   opAt 1637 .LT,
   opAt 1638 .OR,
   opAt 1639 (.Swap ⟨3, by decide⟩),
   opAt 1640 (.Dup ⟨1, by decide⟩),
   opAt 1641 .MSTORE,
   pushAt 1642 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1643 .ADD,
   opAt 1644 (.Swap ⟨0, by decide⟩),
   pushAt 1645 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1646 .ADD,
   opAt 1647 (.Swap ⟨0, by decide⟩),
   opAt 1648 (.Swap ⟨1, by decide⟩),
   pushAt 1649 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1650 .ADD,
   opAt 1651 (.Swap ⟨1, by decide⟩),
   pushAt 1652 2 8224,
   opAt 1653 (.Dup ⟨1, by decide⟩),
   opAt 1654 .GT,
   pushAt 1655 2 2493,
   opAt 1656 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2641. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1657 .POP,
   opAt 1658 .POP,
   opAt 1659 .POP,
   pushAt 1660 2 8224,
   opAt 1661 .MSTORE]

/-- Instructions 1667..1682, pc 2642..2665. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1662 .JUMPDEST,
   pushAt 1663 2 9440,
   opAt 1664 .MLOAD,
   pushAt 1665 2 9408,
   opAt 1666 .MLOAD,
   opAt 1667 (.Dup ⟨1, by decide⟩),
   pushAt 1668 2 7168,
   opAt 1669 .ADD,
   pushAt 1670 2 8256,
   opAt 1671 (.Swap ⟨0, by decide⟩),
   opAt 1672 .SUB,
   pushAt 1673 0 0,
   opAt 1674 (.Swap ⟨2, by decide⟩),
   opAt 1675 (.Swap ⟨0, by decide⟩),
   opAt 1676 (.Swap ⟨1, by decide⟩),
   opAt 1677 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
