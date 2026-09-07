import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (original instructions 1683..1741;
relocated indices 1708..1766). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Original block `1683`, now instructions 1708..1748, pc 2695..2835. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1708 .JUMPDEST,
   opAt 1709 (.Dup ⟨0, by decide⟩),
   opAt 1710 .MLOAD,
   opAt 1711 (.Dup ⟨2, by decide⟩),
   opAt 1712 .MLOAD,
   opAt 1713 (.Swap ⟨0, by decide⟩),
   opAt 1714 (.Dup ⟨1, by decide⟩),
   opAt 1715 (.Dup ⟨1, by decide⟩),
   opAt 1716 .LT,
   opAt 1717 (.Swap ⟨1, by decide⟩),
   opAt 1718 (.Swap ⟨0, by decide⟩),
   opAt 1719 .SUB,
   opAt 1720 (.Dup ⟨5, by decide⟩),
   opAt 1721 (.Dup ⟨1, by decide⟩),
   opAt 1722 .SUB,
   opAt 1723 (.Swap ⟨0, by decide⟩),
   opAt 1724 (.Dup ⟨6, by decide⟩),
   opAt 1725 (.Swap ⟨0, by decide⟩),
   opAt 1726 .LT,
   opAt 1727 (.Swap ⟨0, by decide⟩),
   opAt 1728 (.Swap ⟨1, by decide⟩),
   opAt 1729 .OR,
   opAt 1730 (.Swap ⟨4, by decide⟩),
   opAt 1731 .POP,
   opAt 1732 (.Dup ⟨3, by decide⟩),
   opAt 1733 .MSTORE,
   pushAt 1734 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1735 .ADD,
   opAt 1736 (.Swap ⟨0, by decide⟩),
   pushAt 1737 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1738 .ADD,
   opAt 1739 (.Swap ⟨0, by decide⟩),
   opAt 1740 (.Swap ⟨1, by decide⟩),
   pushAt 1741 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1742 .ADD,
   opAt 1743 (.Swap ⟨1, by decide⟩),
   pushAt 1744 2 8224,
   opAt 1745 (.Dup ⟨1, by decide⟩),
   opAt 1746 .GT,
   pushAt 1747 2 2695,
   opAt 1748 .JUMPI]

/-- Original block `1724`, now instructions 1749..1766, pc 2836..2891. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1749 .POP,
   opAt 1750 .POP,
   opAt 1751 .POP,
   opAt 1752 .ISZERO,
   pushAt 1753 2 8224,
   opAt 1754 .MLOAD,
   opAt 1755 .OR,
   pushAt 1756 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1757 .MUL,
   pushAt 1758 2 8256,
   opAt 1759 .ADD,
   pushAt 1760 2 9344,
   opAt 1761 .MLOAD,
   opAt 1762 (.Swap ⟨0, by decide⟩),
   opAt 1763 (.Dup ⟨2, by decide⟩),
   opAt 1764 .MCOPY,
   opAt 1765 .POP,
   opAt 1766 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
