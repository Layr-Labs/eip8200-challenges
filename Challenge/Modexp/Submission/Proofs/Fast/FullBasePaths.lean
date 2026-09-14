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
  [opAt 1828 .JUMPDEST,
   opAt 1829 (.Dup ⟨0, by decide⟩),
   opAt 1830 (.Dup ⟨3, by decide⟩),
   opAt 1831 .EQ,
   pushAt 1832 0 0,
   opAt 1833 .MLOAD,
   pushAt 1834 1 255,
   opAt 1835 .SHR,
   opAt 1836 .AND,
   opAt 1837 .ISZERO,
   pushAt 1838 2 2468,
   opAt 1839 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1840 (.Dup ⟨0, by decide⟩),
   pushAt 1841 1 96,
   pushAt 1842 2 256,
   opAt 1843 .CALLDATACOPY,
   pushAt 1844 2 2636,
   pushAt 1845 2 512,
   pushAt 1846 2 256,
   pushAt 1847 2 1536,
   pushAt 1848 2 3546,
   opAt 1849 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1850 .JUMPDEST,
   opAt 1851 (.Dup ⟨2, by decide⟩),
   pushAt 1852 1 31,
   opAt 1853 .ADD,
   pushAt 1854 1 5,
   opAt 1855 .SHR,
   opAt 1856 (.Dup ⟨3, by decide⟩),
   opAt 1857 (.Dup ⟨1, by decide⟩),
   pushAt 1858 1 5,
   opAt 1859 .SHL,
   opAt 1860 .SUB,
   pushAt 1861 1 3,
   opAt 1862 .SHL,
   pushAt 1863 1 96,
   opAt 1864 .CALLDATALOAD,
   opAt 1865 (.Swap ⟨0, by decide⟩),
   opAt 1866 .SHR,
   opAt 1867 (.Dup ⟨2, by decide⟩),
   pushAt 1868 1 224,
   opAt 1869 .ADD,
   opAt 1870 .MSTORE,
   pushAt 1871 1 1,
   pushAt 1872 2 962,
   opAt 1873 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
