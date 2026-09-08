import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1683..1741). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1683..1723, pc 2666..2806. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1651 .JUMPDEST,
   opAt 1652 (.Dup ⟨0, by decide⟩),
   opAt 1653 .MLOAD,
   opAt 1654 (.Dup ⟨2, by decide⟩),
   opAt 1655 .MLOAD,
      opAt 1656 (.Dup ⟨1, by decide⟩),
   opAt 1657 (.Dup ⟨1, by decide⟩),
   opAt 1658 .GT,
   opAt 1659 (.Swap ⟨1, by decide⟩),
      opAt 1660 .SUB,
   opAt 1661 (.Dup ⟨5, by decide⟩),
   opAt 1662 (.Dup ⟨1, by decide⟩),
   opAt 1663 .SUB,
   opAt 1664 (.Swap ⟨0, by decide⟩),
   opAt 1665 (.Dup ⟨6, by decide⟩),
      opAt 1666 .GT,
   opAt 1667 (.Swap ⟨0, by decide⟩),
   opAt 1668 (.Swap ⟨1, by decide⟩),
   opAt 1669 .OR,
   opAt 1670 (.Swap ⟨4, by decide⟩),
   opAt 1671 .POP,
   opAt 1672 (.Dup ⟨3, by decide⟩),
   opAt 1673 .MSTORE,
   pushAt 1674 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1675 .ADD,
   opAt 1676 (.Swap ⟨0, by decide⟩),
   pushAt 1677 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1678 .ADD,
   opAt 1679 (.Swap ⟨0, by decide⟩),
   opAt 1680 (.Swap ⟨1, by decide⟩),
   pushAt 1681 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1682 .ADD,
   opAt 1683 (.Swap ⟨1, by decide⟩),
   pushAt 1684 2 8224,
   opAt 1685 (.Dup ⟨1, by decide⟩),
   opAt 1686 .GT,
   pushAt 1687 2 2520,
   opAt 1688 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1689 .POP,
   opAt 1690 .POP,
   opAt 1691 .POP,
   opAt 1692 .ISZERO,
   pushAt 1693 2 8224,
   opAt 1694 .MLOAD,
   opAt 1695 .OR,
   pushAt 1696 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1697 .MUL,
   pushAt 1698 2 8256,
   opAt 1699 .ADD,
   pushAt 1700 2 9344,
   opAt 1701 .MLOAD,
   opAt 1702 (.Swap ⟨1, by decide⟩),
   opAt 1703 .MCOPY,
   opAt 1704 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
