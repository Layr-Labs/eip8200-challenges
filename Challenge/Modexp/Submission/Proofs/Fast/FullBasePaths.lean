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
  [opAt 1751 .JUMPDEST,
   opAt 1752 (.Dup ⟨0, by decide⟩),
   opAt 1753 (.Dup ⟨3, by decide⟩),
   opAt 1754 .EQ,
   pushAt 1755 0 0,
   opAt 1756 .MLOAD,
   pushAt 1757 1 255,
   opAt 1758 .SHR,
   opAt 1759 .AND,
   opAt 1760 .ISZERO,
   pushAt 1761 2 2343,
   opAt 1762 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1763 (.Dup ⟨0, by decide⟩),
   pushAt 1764 1 96,
   pushAt 1765 2 256,
   opAt 1766 .CALLDATACOPY,
   pushAt 1767 2 2443,
   pushAt 1768 2 512,
   pushAt 1769 2 256,
   pushAt 1770 2 1536,
   pushAt 1771 2 3353,
   opAt 1772 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1773 .JUMPDEST,
   opAt 1774 (.Dup ⟨2, by decide⟩),
   pushAt 1775 1 31,
   opAt 1776 .ADD,
   pushAt 1777 1 5,
   opAt 1778 .SHR,
   opAt 1779 (.Dup ⟨3, by decide⟩),
   opAt 1780 (.Dup ⟨1, by decide⟩),
   pushAt 1781 1 5,
   opAt 1782 .SHL,
   opAt 1783 .SUB,
   pushAt 1784 1 3,
   opAt 1785 .SHL,
   pushAt 1786 1 96,
   opAt 1787 .CALLDATALOAD,
   opAt 1788 (.Swap ⟨0, by decide⟩),
   opAt 1789 .SHR,
   opAt 1790 (.Dup ⟨2, by decide⟩),
   pushAt 1791 1 224,
   opAt 1792 .ADD,
   opAt 1793 .MSTORE,
   pushAt 1794 1 1,
   pushAt 1795 2 853,
   opAt 1796 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
