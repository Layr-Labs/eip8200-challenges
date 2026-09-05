import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Complete dispatcher path when the relocated first exponent byte is neither one nor three. -/
def blk1768 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1768 .JUMPDEST,
   opAt 1769 (.Dup ⟨3, by decide⟩),
   opAt 1770 .ISZERO,
   pushAt 1771 2 1756,
   opAt 1772 .JUMPI,
   pushAt 1773 2 9472,
   opAt 1774 .MLOAD,
   opAt 1775 .CALLDATALOAD,
   pushAt 1776 0 0,
   opAt 1777 .BYTE,
   opAt 1778 (.Dup ⟨0, by decide⟩),
   pushAt 1779 1 1,
   opAt 1780 .EQ,
   pushAt 1781 2 2934,
   opAt 1782 .JUMPI,
   pushAt 1783 1 3,
   opAt 1784 .EQ,
   pushAt 1785 2 2953,
   opAt 1786 .JUMPI,
   pushAt 1787 2 1756,
   opAt 1788 .JUMP]

/-- Taken dispatcher prefix for the empty-exponent branch. -/
def blk1768empty :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1768 .JUMPDEST,
   opAt 1769 (.Dup ⟨3, by decide⟩),
   opAt 1770 .ISZERO,
   pushAt 1771 2 1756,
   opAt 1772 .JUMPI]

/-- Taken dispatcher prefix for the first-byte-is-one branch. -/
def blk1768one :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1768 .JUMPDEST,
   opAt 1769 (.Dup ⟨3, by decide⟩),
   opAt 1770 .ISZERO,
   pushAt 1771 2 1756,
   opAt 1772 .JUMPI,
   pushAt 1773 2 9472,
   opAt 1774 .MLOAD,
   opAt 1775 .CALLDATALOAD,
   pushAt 1776 0 0,
   opAt 1777 .BYTE,
   opAt 1778 (.Dup ⟨0, by decide⟩),
   pushAt 1779 1 1,
   opAt 1780 .EQ,
   pushAt 1781 2 2934,
   opAt 1782 .JUMPI]

/-- Taken dispatcher prefix for the first-byte-is-three branch. -/
def blk1768three :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1768 .JUMPDEST,
   opAt 1769 (.Dup ⟨3, by decide⟩),
   opAt 1770 .ISZERO,
   pushAt 1771 2 1756,
   opAt 1772 .JUMPI,
   pushAt 1773 2 9472,
   opAt 1774 .MLOAD,
   opAt 1775 .CALLDATALOAD,
   pushAt 1776 0 0,
   opAt 1777 .BYTE,
   opAt 1778 (.Dup ⟨0, by decide⟩),
   pushAt 1779 1 1,
   opAt 1780 .EQ,
   pushAt 1781 2 2934,
   opAt 1782 .JUMPI,
   pushAt 1783 1 3,
   opAt 1784 .EQ,
   pushAt 1785 2 2953,
   opAt 1786 .JUMPI]

/-- Copy `BASE` to `ACC` and continue at exponent byte one. -/
def blk1789 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1789 .JUMPDEST,
   opAt 1790 .POP,
   pushAt 1791 2 9344,
   opAt 1792 .MLOAD,
   pushAt 1793 2 2048,
   pushAt 1794 2 1024,
   opAt 1795 .MCOPY,
   pushAt 1796 1 1,
   pushAt 1797 2 1769,
   opAt 1798 .JUMP]

/-- Copy Montgomery one to `ACC` and enter the last two bits of byte zero. -/
def blk1799 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1799 .JUMPDEST,
   pushAt 1800 2 9344,
   opAt 1801 .MLOAD,
   pushAt 1802 2 4096,
   pushAt 1803 2 1024,
   opAt 1804 .MCOPY,
   pushAt 1805 0 0,
   pushAt 1806 1 3,
   pushAt 1807 1 2,
   pushAt 1808 2 1789,
   opAt 1809 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
