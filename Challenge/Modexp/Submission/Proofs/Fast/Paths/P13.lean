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
  [opAt 1684 .JUMPDEST,
   opAt 1685 (.Dup ⟨0, by decide⟩),
   opAt 1686 .MLOAD,
   opAt 1687 (.Dup ⟨2, by decide⟩),
   opAt 1688 .MLOAD,
   opAt 1689 (.Swap ⟨0, by decide⟩),
   opAt 1690 (.Dup ⟨1, by decide⟩),
   opAt 1691 (.Dup ⟨1, by decide⟩),
   opAt 1692 .LT,
   opAt 1693 (.Swap ⟨1, by decide⟩),
   opAt 1694 (.Swap ⟨0, by decide⟩),
   opAt 1695 .SUB,
   opAt 1696 (.Dup ⟨5, by decide⟩),
   opAt 1697 (.Dup ⟨1, by decide⟩),
   opAt 1698 .SUB,
   opAt 1699 (.Swap ⟨0, by decide⟩),
   opAt 1700 (.Dup ⟨6, by decide⟩),
   opAt 1701 (.Swap ⟨0, by decide⟩),
   opAt 1702 .LT,
   opAt 1703 (.Swap ⟨0, by decide⟩),
   opAt 1704 (.Swap ⟨1, by decide⟩),
   opAt 1705 .OR,
   opAt 1706 (.Swap ⟨4, by decide⟩),
   opAt 1707 .POP,
   opAt 1708 (.Dup ⟨3, by decide⟩),
   opAt 1709 .MSTORE,
   pushAt 1710 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1711 .ADD,
   opAt 1712 (.Swap ⟨0, by decide⟩),
   pushAt 1713 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1714 .ADD,
   opAt 1715 (.Swap ⟨0, by decide⟩),
   opAt 1716 (.Swap ⟨1, by decide⟩),
   pushAt 1717 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1718 .ADD,
   opAt 1719 (.Swap ⟨1, by decide⟩),
   pushAt 1720 2 8224,
   opAt 1721 (.Dup ⟨1, by decide⟩),
   opAt 1722 .GT,
   pushAt 1723 2 2666,
   opAt 1724 .JUMPI]

/-- Instructions 1724..1741, pc 2807..2862. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1725 .POP,
   opAt 1726 .POP,
   opAt 1727 .POP,
   opAt 1728 .ISZERO,
   pushAt 1729 2 8224,
   opAt 1730 .MLOAD,
   opAt 1731 .OR,
   pushAt 1732 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1733 .MUL,
   pushAt 1734 2 8256,
   opAt 1735 .ADD,
   pushAt 1736 2 9344,
   opAt 1737 .MLOAD,
   opAt 1738 (.Swap ⟨0, by decide⟩),
   opAt 1739 (.Dup ⟨2, by decide⟩),
   opAt 1740 .MCOPY,
   opAt 1741 .POP,
   opAt 1742 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
