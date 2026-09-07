import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (original instructions 1683..1741;
relocated indices 1714..1772). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Original block `1683`, now instructions 1714..1754, pc 2710..2850. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1714 .JUMPDEST,
   opAt 1715 (.Dup ⟨0, by decide⟩),
   opAt 1716 .MLOAD,
   opAt 1717 (.Dup ⟨2, by decide⟩),
   opAt 1718 .MLOAD,
   opAt 1719 (.Swap ⟨0, by decide⟩),
   opAt 1720 (.Dup ⟨1, by decide⟩),
   opAt 1721 (.Dup ⟨1, by decide⟩),
   opAt 1722 .LT,
   opAt 1723 (.Swap ⟨1, by decide⟩),
   opAt 1724 (.Swap ⟨0, by decide⟩),
   opAt 1725 .SUB,
   opAt 1726 (.Dup ⟨5, by decide⟩),
   opAt 1727 (.Dup ⟨1, by decide⟩),
   opAt 1728 .SUB,
   opAt 1729 (.Swap ⟨0, by decide⟩),
   opAt 1730 (.Dup ⟨6, by decide⟩),
   opAt 1731 (.Swap ⟨0, by decide⟩),
   opAt 1732 .LT,
   opAt 1733 (.Swap ⟨0, by decide⟩),
   opAt 1734 (.Swap ⟨1, by decide⟩),
   opAt 1735 .OR,
   opAt 1736 (.Swap ⟨4, by decide⟩),
   opAt 1737 .POP,
   opAt 1738 (.Dup ⟨3, by decide⟩),
   opAt 1739 .MSTORE,
   pushAt 1740 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1741 .ADD,
   opAt 1742 (.Swap ⟨0, by decide⟩),
   pushAt 1743 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1744 .ADD,
   opAt 1745 (.Swap ⟨0, by decide⟩),
   opAt 1746 (.Swap ⟨1, by decide⟩),
   pushAt 1747 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1748 .ADD,
   opAt 1749 (.Swap ⟨1, by decide⟩),
   pushAt 1750 2 8224,
   opAt 1751 (.Dup ⟨1, by decide⟩),
   opAt 1752 .GT,
   pushAt 1753 2 2710,
   opAt 1754 .JUMPI]

/-- Original block `1724`, now instructions 1755..1772, pc 2851..2906. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1755 .POP,
   opAt 1756 .POP,
   opAt 1757 .POP,
   opAt 1758 .ISZERO,
   pushAt 1759 2 8224,
   opAt 1760 .MLOAD,
   opAt 1761 .OR,
   pushAt 1762 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1763 .MUL,
   pushAt 1764 2 8256,
   opAt 1765 .ADD,
   pushAt 1766 2 9344,
   opAt 1767 .MLOAD,
   opAt 1768 (.Swap ⟨0, by decide⟩),
   opAt 1769 (.Dup ⟨2, by decide⟩),
   opAt 1770 .MCOPY,
   opAt 1771 .POP,
   opAt 1772 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
