import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Complete dispatcher path when the first exponent byte is neither one nor three. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1742 .JUMPDEST,
   opAt 1743 (.Dup ⟨3, by decide⟩),
   opAt 1744 .ISZERO,
   pushAt 1745 2 1756,
   opAt 1746 .JUMPI,
   pushAt 1747 2 9472,
   opAt 1748 .MLOAD,
   opAt 1749 .CALLDATALOAD,
   pushAt 1750 0 0,
   opAt 1751 .BYTE,
   opAt 1752 (.Dup ⟨0, by decide⟩),
   pushAt 1753 1 1,
   opAt 1754 .EQ,
   pushAt 1755 2 2896,
   opAt 1756 .JUMPI,
   pushAt 1757 1 3,
   opAt 1758 .EQ,
   pushAt 1759 2 2915,
   opAt 1760 .JUMPI,
   pushAt 1761 2 1756,
   opAt 1762 .JUMP]

/-- Taken dispatcher prefix for the empty-exponent branch. -/
def blk1742empty :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1742 .JUMPDEST,
   opAt 1743 (.Dup ⟨3, by decide⟩),
   opAt 1744 .ISZERO,
   pushAt 1745 2 1756,
   opAt 1746 .JUMPI]

/-- Taken dispatcher prefix for the first-byte-is-one branch. -/
def blk1742one :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1742 .JUMPDEST,
   opAt 1743 (.Dup ⟨3, by decide⟩),
   opAt 1744 .ISZERO,
   pushAt 1745 2 1756,
   opAt 1746 .JUMPI,
   pushAt 1747 2 9472,
   opAt 1748 .MLOAD,
   opAt 1749 .CALLDATALOAD,
   pushAt 1750 0 0,
   opAt 1751 .BYTE,
   opAt 1752 (.Dup ⟨0, by decide⟩),
   pushAt 1753 1 1,
   opAt 1754 .EQ,
   pushAt 1755 2 2896,
   opAt 1756 .JUMPI]

/-- Taken dispatcher prefix for the first-byte-is-three branch. -/
def blk1742three :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1742 .JUMPDEST,
   opAt 1743 (.Dup ⟨3, by decide⟩),
   opAt 1744 .ISZERO,
   pushAt 1745 2 1756,
   opAt 1746 .JUMPI,
   pushAt 1747 2 9472,
   opAt 1748 .MLOAD,
   opAt 1749 .CALLDATALOAD,
   pushAt 1750 0 0,
   opAt 1751 .BYTE,
   opAt 1752 (.Dup ⟨0, by decide⟩),
   pushAt 1753 1 1,
   opAt 1754 .EQ,
   pushAt 1755 2 2896,
   opAt 1756 .JUMPI,
   pushAt 1757 1 3,
   opAt 1758 .EQ,
   pushAt 1759 2 2915,
   opAt 1760 .JUMPI]

/-- Copy `BASE` to `ACC` and continue at exponent byte one. -/
def blk1763 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1763 .JUMPDEST,
   opAt 1764 .POP,
   pushAt 1765 2 9344,
   opAt 1766 .MLOAD,
   pushAt 1767 2 2048,
   pushAt 1768 2 1024,
   opAt 1769 .MCOPY,
   pushAt 1770 1 1,
   pushAt 1771 2 1769,
   opAt 1772 .JUMP]

/-- Copy the Montgomery base to `ACC` and enter the final bit of byte zero. -/
def blk1773 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1773 .JUMPDEST,
   pushAt 1774 2 9344,
   opAt 1775 .MLOAD,
   pushAt 1776 2 2048,
   pushAt 1777 2 1024,
   opAt 1778 .MCOPY,
   pushAt 1779 0 0,
   pushAt 1780 1 3,
   pushAt 1781 1 1,
   pushAt 1782 2 1789,
   opAt 1783 .JUMP]


/-- Instructions 1784..1790, pc 2936..2946: `CCB` entry, `ADDMOD(px, px) → px`. -/
def blk1784 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1784 .JUMPDEST,
   pushAt 1785 2 2947,
   opAt 1786 (.Dup ⟨1, by decide⟩),
   opAt 1787 (.Dup ⟨0, by decide⟩),
   opAt 1788 (.Dup ⟨0, by decide⟩),
   pushAt 1789 2 2467,
   opAt 1790 .JUMP]

/-- Instructions 1791..1792, pc 2947..2949: the squaring counter. -/
def blk1791 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1791 .JUMPDEST,
   pushAt 1792 1 8]

/-- Instructions 1793..1799, pc 2950..2960: `MONPRO(px, px) → px`. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1793 .JUMPDEST,
   pushAt 1794 2 2961,
   opAt 1795 (.Dup ⟨2, by decide⟩),
   opAt 1796 (.Dup ⟨0, by decide⟩),
   opAt 1797 (.Dup ⟨0, by decide⟩),
   pushAt 1798 2 1939,
   opAt 1799 .JUMP]

/-- Instructions 1800..1806, pc 2961..2970: decrement and loop back. -/
def blk1800 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1800 .JUMPDEST,
   pushAt 1801 1 1,
   opAt 1802 (.Swap ⟨0, by decide⟩),
   opAt 1803 .SUB,
   opAt 1804 (.Dup ⟨0, by decide⟩),
   pushAt 1805 2 2950,
   opAt 1806 .JUMPI]

/-- Instructions 1807..1809, pc 2971..2973: drop the counter and return. -/
def blk1807 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1807 .POP,
   opAt 1808 .POP,
   opAt 1809 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
