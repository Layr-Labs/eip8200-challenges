import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def blkPrefix :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1782 .JUMPDEST,
   opAt 1783 (.Dup ⟨3, by decide⟩),
   opAt 1784 .ISZERO,
   pushAt 1785 2 1756,
   opAt 1786 .JUMPI,
   pushAt 1787 2 9472,
   opAt 1788 .MLOAD,
   opAt 1789 .CALLDATALOAD,
   pushAt 1790 0 0,
   opAt 1791 .BYTE,
   opAt 1792 (.Dup ⟨0, by decide⟩),
   pushAt 1793 1 1,
   opAt 1794 .EQ,
   pushAt 1795 2 2955,
   opAt 1796 .JUMPI,
   pushAt 1797 1 3,
   opAt 1798 .EQ,
   pushAt 1799 2 2974,
   opAt 1800 .JUMPI,
   pushAt 1801 2 1756,
   opAt 1802 .JUMP]

def blkPrefixEmpty :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1782 .JUMPDEST,
   opAt 1783 (.Dup ⟨3, by decide⟩),
   opAt 1784 .ISZERO,
   pushAt 1785 2 1756,
   opAt 1786 .JUMPI]

def blkPrefixOne :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1782 .JUMPDEST,
   opAt 1783 (.Dup ⟨3, by decide⟩),
   opAt 1784 .ISZERO,
   pushAt 1785 2 1756,
   opAt 1786 .JUMPI,
   pushAt 1787 2 9472,
   opAt 1788 .MLOAD,
   opAt 1789 .CALLDATALOAD,
   pushAt 1790 0 0,
   opAt 1791 .BYTE,
   opAt 1792 (.Dup ⟨0, by decide⟩),
   pushAt 1793 1 1,
   opAt 1794 .EQ,
   pushAt 1795 2 2955,
   opAt 1796 .JUMPI]

def blkPrefixThree :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1782 .JUMPDEST,
   opAt 1783 (.Dup ⟨3, by decide⟩),
   opAt 1784 .ISZERO,
   pushAt 1785 2 1756,
   opAt 1786 .JUMPI,
   pushAt 1787 2 9472,
   opAt 1788 .MLOAD,
   opAt 1789 .CALLDATALOAD,
   pushAt 1790 0 0,
   opAt 1791 .BYTE,
   opAt 1792 (.Dup ⟨0, by decide⟩),
   pushAt 1793 1 1,
   opAt 1794 .EQ,
   pushAt 1795 2 2955,
   opAt 1796 .JUMPI,
   pushAt 1797 1 3,
   opAt 1798 .EQ,
   pushAt 1799 2 2974,
   opAt 1800 .JUMPI]

def blkPrefixOneBody :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1803 .JUMPDEST,
   opAt 1804 .POP,
   pushAt 1805 2 9344,
   opAt 1806 .MLOAD,
   pushAt 1807 2 2048,
   pushAt 1808 2 1024,
   opAt 1809 .MCOPY,
   pushAt 1810 1 1,
   pushAt 1811 2 1769,
   opAt 1812 .JUMP]

def blkPrefixThreeBody :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1813 .JUMPDEST,
   pushAt 1814 2 9344,
   opAt 1815 .MLOAD,
   pushAt 1816 2 4096,
   pushAt 1817 2 1024,
   opAt 1818 .MCOPY,
   pushAt 1819 0 0,
   pushAt 1820 1 3,
   pushAt 1821 1 2,
   pushAt 1822 2 1789,
   opAt 1823 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
