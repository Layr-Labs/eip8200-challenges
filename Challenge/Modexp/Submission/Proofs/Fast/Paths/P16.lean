import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Complete dispatcher path when the first exponent byte is neither one nor three. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1781 .JUMPDEST,
   opAt 1782 (.Dup ⟨3, by decide⟩),
   opAt 1783 .ISZERO,
   pushAt 1784 2 1756,
   opAt 1785 .JUMPI,
   pushAt 1786 2 9472,
   opAt 1787 .MLOAD,
   opAt 1788 .CALLDATALOAD,
   pushAt 1789 0 0,
   opAt 1790 .BYTE,
   opAt 1791 (.Dup ⟨0, by decide⟩),
   pushAt 1792 1 1,
   opAt 1793 .EQ,
   pushAt 1794 2 2955,
   opAt 1795 .JUMPI,
   pushAt 1796 1 3,
   opAt 1797 .EQ,
   pushAt 1798 2 2974,
   opAt 1799 .JUMPI,
   pushAt 1800 2 1756,
   opAt 1801 .JUMP]

/-- Taken dispatcher prefix for the empty-exponent branch. -/
def blk1781empty :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1781 .JUMPDEST,
   opAt 1782 (.Dup ⟨3, by decide⟩),
   opAt 1783 .ISZERO,
   pushAt 1784 2 1756,
   opAt 1785 .JUMPI]

/-- Taken dispatcher prefix for the first-byte-is-one branch. -/
def blk1781one :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1781 .JUMPDEST,
   opAt 1782 (.Dup ⟨3, by decide⟩),
   opAt 1783 .ISZERO,
   pushAt 1784 2 1756,
   opAt 1785 .JUMPI,
   pushAt 1786 2 9472,
   opAt 1787 .MLOAD,
   opAt 1788 .CALLDATALOAD,
   pushAt 1789 0 0,
   opAt 1790 .BYTE,
   opAt 1791 (.Dup ⟨0, by decide⟩),
   pushAt 1792 1 1,
   opAt 1793 .EQ,
   pushAt 1794 2 2955,
   opAt 1795 .JUMPI]

/-- Taken dispatcher prefix for the first-byte-is-three branch. -/
def blk1781three :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1781 .JUMPDEST,
   opAt 1782 (.Dup ⟨3, by decide⟩),
   opAt 1783 .ISZERO,
   pushAt 1784 2 1756,
   opAt 1785 .JUMPI,
   pushAt 1786 2 9472,
   opAt 1787 .MLOAD,
   opAt 1788 .CALLDATALOAD,
   pushAt 1789 0 0,
   opAt 1790 .BYTE,
   opAt 1791 (.Dup ⟨0, by decide⟩),
   pushAt 1792 1 1,
   opAt 1793 .EQ,
   pushAt 1794 2 2955,
   opAt 1795 .JUMPI,
   pushAt 1796 1 3,
   opAt 1797 .EQ,
   pushAt 1798 2 2974,
   opAt 1799 .JUMPI]

/-- Copy `BASE` to `ACC` and continue at exponent byte one. -/
def blk1802 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1802 .JUMPDEST,
   opAt 1803 .POP,
   pushAt 1804 2 9344,
   opAt 1805 .MLOAD,
   pushAt 1806 2 2048,
   pushAt 1807 2 1024,
   opAt 1808 .MCOPY,
   pushAt 1809 1 1,
   pushAt 1810 2 1769,
   opAt 1811 .JUMP]

/-- Copy Montgomery one to `ACC` and enter the last two bits of byte zero. -/
def blk1812 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1812 .JUMPDEST,
   pushAt 1813 2 9344,
   opAt 1814 .MLOAD,
   pushAt 1815 2 4096,
   pushAt 1816 2 1024,
   opAt 1817 .MCOPY,
   pushAt 1818 0 0,
   pushAt 1819 1 3,
   pushAt 1820 1 2,
   pushAt 1821 2 1789,
   opAt 1822 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
