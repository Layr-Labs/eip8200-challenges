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
  [opAt 1752 .JUMPDEST,
   opAt 1753 (.Dup ⟨0, by decide⟩),
   opAt 1754 (.Dup ⟨3, by decide⟩),
   opAt 1755 .EQ,
   pushAt 1756 0 0,
   opAt 1757 .MLOAD,
   pushAt 1758 1 255,
   opAt 1759 .SHR,
   opAt 1760 .AND,
   opAt 1761 .ISZERO,
   pushAt 1762 2 2343,
   opAt 1763 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1764 (.Dup ⟨0, by decide⟩),
   pushAt 1765 1 96,
   pushAt 1766 2 256,
   opAt 1767 .CALLDATACOPY,
   pushAt 1768 2 2443,
   pushAt 1769 2 512,
   pushAt 1770 2 256,
   pushAt 1771 2 1536,
   pushAt 1772 2 3353,
   opAt 1773 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1774 .JUMPDEST,
   opAt 1775 (.Dup ⟨2, by decide⟩),
   pushAt 1776 1 31,
   opAt 1777 .ADD,
   pushAt 1778 1 5,
   opAt 1779 .SHR,
   opAt 1780 (.Dup ⟨3, by decide⟩),
   opAt 1781 (.Dup ⟨1, by decide⟩),
   pushAt 1782 1 5,
   opAt 1783 .SHL,
   opAt 1784 .SUB,
   pushAt 1785 1 3,
   opAt 1786 .SHL,
   pushAt 1787 1 96,
   opAt 1788 .CALLDATALOAD,
   opAt 1789 (.Swap ⟨0, by decide⟩),
   opAt 1790 .SHR,
   opAt 1791 (.Dup ⟨2, by decide⟩),
   pushAt 1792 1 224,
   opAt 1793 .ADD,
   opAt 1794 .MSTORE,
   pushAt 1795 1 1,
   pushAt 1796 2 853,
   opAt 1797 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
