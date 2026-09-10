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
  [opAt 1620 .JUMPDEST,
   opAt 1621 (.Dup ⟨0, by decide⟩),
   opAt 1622 .MLOAD,
   opAt 1623 (.Dup ⟨2, by decide⟩),
   opAt 1624 .MLOAD,
   opAt 1625 (.Dup ⟨1, by decide⟩),
   opAt 1626 (.Dup ⟨1, by decide⟩),
   opAt 1627 .GT,
   opAt 1628 (.Swap ⟨1, by decide⟩),
   opAt 1629 .SUB,
   opAt 1630 (.Dup ⟨5, by decide⟩),
   opAt 1631 (.Dup ⟨1, by decide⟩),
   opAt 1632 .SUB,
   opAt 1633 (.Swap ⟨0, by decide⟩),
   opAt 1634 (.Dup ⟨6, by decide⟩),
   opAt 1635 .GT,
   opAt 1636 (.Swap ⟨0, by decide⟩),
   opAt 1637 (.Swap ⟨1, by decide⟩),
   opAt 1638 .OR,
   opAt 1639 (.Swap ⟨4, by decide⟩),
   opAt 1640 .POP,
   opAt 1641 (.Dup ⟨3, by decide⟩),
   opAt 1642 .MSTORE,
   pushAt 1643 1 31,
   opAt 1644 .NOT,
   opAt 1645 .ADD,
   opAt 1646 (.Swap ⟨0, by decide⟩),
   pushAt 1647 1 31,
   opAt 1648 .NOT,
   opAt 1649 .ADD,
   opAt 1650 (.Swap ⟨0, by decide⟩),
   opAt 1651 (.Swap ⟨1, by decide⟩),
   pushAt 1652 1 31,
   opAt 1653 .NOT,
   opAt 1654 .ADD,
   opAt 1655 (.Swap ⟨1, by decide⟩),
   pushAt 1656 2 8224,
   opAt 1657 (.Dup ⟨1, by decide⟩),
   opAt 1658 .GT,
   pushAt 1659 2 2225,
   opAt 1660 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1661 .POP,
   opAt 1662 .POP,
   opAt 1663 .POP,
   opAt 1664 .ISZERO,
   pushAt 1665 2 8224,
   opAt 1666 .MLOAD,
   opAt 1667 .OR,
   pushAt 1668 2 1087,
   opAt 1669 .NOT,
   opAt 1670 .MUL,
   pushAt 1671 2 8256,
   opAt 1672 .ADD,
   pushAt 1673 2 9344,
   opAt 1674 .MLOAD,
   opAt 1675 (.Swap ⟨1, by decide⟩),
   opAt 1676 .MCOPY,
   opAt 1677 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
