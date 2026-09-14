import Challenge.Modexp.Submission.Proofs.Fast.Paths.P4
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located paths for the full-width-base helper

The helper is appended after the fixed-window and direct-RR helpers. Its miss
path reproduces the original base-head computation before jumping to the
unchanged base loop at pc 1795.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1753 .JUMPDEST,
   opAt 1754 (.Dup ⟨0, by decide⟩),
   opAt 1755 (.Dup ⟨3, by decide⟩),
   opAt 1756 .EQ,
   pushAt 1757 0 0,
   opAt 1758 .MLOAD,
   pushAt 1759 1 255,
   opAt 1760 .SHR,
   opAt 1761 .AND,
   opAt 1762 .ISZERO,
   pushAt 1763 2 2343,
   opAt 1764 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1765 (.Dup ⟨0, by decide⟩),
   pushAt 1766 1 96,
   pushAt 1767 2 256,
   opAt 1768 .CALLDATACOPY,
   pushAt 1769 2 2443,
   pushAt 1770 2 512,
   pushAt 1771 2 256,
   pushAt 1772 2 1536,
   pushAt 1773 2 3353,
   opAt 1774 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1775 .JUMPDEST,
   opAt 1776 (.Dup ⟨2, by decide⟩),
   pushAt 1777 1 31,
   opAt 1778 .ADD,
   pushAt 1779 1 5,
   opAt 1780 .SHR,
   opAt 1781 (.Dup ⟨3, by decide⟩),
   opAt 1782 (.Dup ⟨1, by decide⟩),
   pushAt 1783 1 5,
   opAt 1784 .SHL,
   opAt 1785 .SUB,
   pushAt 1786 1 3,
   opAt 1787 .SHL,
   pushAt 1788 1 96,
   opAt 1789 .CALLDATALOAD,
   opAt 1790 (.Swap ⟨0, by decide⟩),
   opAt 1791 .SHR,
   opAt 1792 (.Dup ⟨2, by decide⟩),
   pushAt 1793 1 224,
   opAt 1794 .ADD,
   opAt 1795 .MSTORE,
   pushAt 1796 1 1,
   pushAt 1797 2 853,
   opAt 1798 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
