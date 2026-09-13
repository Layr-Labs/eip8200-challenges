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
  [opAt 1834 .JUMPDEST,
   opAt 1835 (.Dup ⟨0, by decide⟩),
   opAt 1836 (.Dup ⟨3, by decide⟩),
   opAt 1837 .EQ,
   pushAt 1838 0 0,
   opAt 1839 .MLOAD,
   pushAt 1840 1 255,
   opAt 1841 .SHR,
   opAt 1842 .AND,
   opAt 1843 .ISZERO,
   pushAt 1844 2 2468,
   opAt 1845 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1846 (.Dup ⟨0, by decide⟩),
   pushAt 1847 1 96,
   pushAt 1848 2 256,
   opAt 1849 .CALLDATACOPY,
   pushAt 1850 2 2638,
   pushAt 1851 2 512,
   pushAt 1852 2 256,
   pushAt 1853 2 1536,
   pushAt 1854 2 3552,
   opAt 1855 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1856 .JUMPDEST,
   opAt 1857 (.Dup ⟨2, by decide⟩),
   pushAt 1858 1 31,
   opAt 1859 .ADD,
   pushAt 1860 1 5,
   opAt 1861 .SHR,
   opAt 1862 (.Dup ⟨3, by decide⟩),
   opAt 1863 (.Dup ⟨1, by decide⟩),
   pushAt 1864 1 5,
   opAt 1865 .SHL,
   opAt 1866 .SUB,
   pushAt 1867 1 3,
   opAt 1868 .SHL,
   pushAt 1869 1 96,
   opAt 1870 .CALLDATALOAD,
   opAt 1871 (.Swap ⟨0, by decide⟩),
   opAt 1872 .SHR,
   opAt 1873 (.Dup ⟨2, by decide⟩),
   pushAt 1874 1 224,
   opAt 1875 .ADD,
   opAt 1876 .MSTORE,
   pushAt 1877 1 1,
   pushAt 1878 2 963,
   opAt 1879 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
