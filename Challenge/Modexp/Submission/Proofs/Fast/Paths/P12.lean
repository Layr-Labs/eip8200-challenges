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
  [opAt 1628 .JUMPDEST,
   opAt 1629 (.Dup ⟨1, by decide⟩),
   opAt 1630 .MLOAD,
   opAt 1631 (.Dup ⟨3, by decide⟩),
   opAt 1632 .MLOAD,
   opAt 1633 (.Dup ⟨1, by decide⟩),
   opAt 1634 .ADD,
   opAt 1635 (.Swap ⟨0, by decide⟩),
   opAt 1636 (.Dup ⟨1, by decide⟩),
   opAt 1637 .LT,
   opAt 1638 (.Swap ⟨0, by decide⟩),
   opAt 1639 (.Dup ⟨5, by decide⟩),
   opAt 1640 .ADD,
   opAt 1641 (.Swap ⟨4, by decide⟩),
   opAt 1642 (.Dup ⟨5, by decide⟩),
   opAt 1643 .LT,
   opAt 1644 .OR,
   opAt 1645 (.Swap ⟨3, by decide⟩),
   opAt 1646 (.Dup ⟨1, by decide⟩),
   opAt 1647 .MSTORE,
   pushAt 1648 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1649 .ADD,
   opAt 1650 (.Swap ⟨0, by decide⟩),
   pushAt 1651 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1652 .ADD,
   opAt 1653 (.Swap ⟨0, by decide⟩),
   opAt 1654 (.Swap ⟨1, by decide⟩),
   pushAt 1655 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1656 .ADD,
   opAt 1657 (.Swap ⟨1, by decide⟩),
   pushAt 1658 2 8224,
   opAt 1659 (.Dup ⟨1, by decide⟩),
   opAt 1660 .GT,
   pushAt 1661 2 2500,
   opAt 1662 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2641. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1663 .POP,
   opAt 1664 .POP,
   opAt 1665 .POP,
   pushAt 1666 2 8224,
   opAt 1667 .MSTORE]

/-- Instructions 1667..1682, pc 2642..2665. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1668 .JUMPDEST,
   pushAt 1669 2 9440,
   opAt 1670 .MLOAD,
   pushAt 1671 2 9408,
   opAt 1672 .MLOAD,
   opAt 1673 (.Dup ⟨1, by decide⟩),
   pushAt 1674 2 7168,
   opAt 1675 .ADD,
   pushAt 1676 2 8256,
   opAt 1677 (.Swap ⟨0, by decide⟩),
   opAt 1678 .SUB,
   pushAt 1679 0 0,
   opAt 1680 (.Swap ⟨2, by decide⟩),
   opAt 1681 (.Swap ⟨0, by decide⟩),
   opAt 1682 (.Swap ⟨1, by decide⟩),
   opAt 1683 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
