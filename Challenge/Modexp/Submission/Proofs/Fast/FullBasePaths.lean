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
  [opAt 1840 .JUMPDEST,
   opAt 1841 (.Dup ⟨0, by decide⟩),
   opAt 1842 (.Dup ⟨3, by decide⟩),
   opAt 1843 .EQ,
   pushAt 1844 0 0,
   opAt 1845 .MLOAD,
   pushAt 1846 1 255,
   opAt 1847 .SHR,
   opAt 1848 .AND,
   opAt 1849 .ISZERO,
   pushAt 1850 2 2472,
   opAt 1851 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1852 (.Dup ⟨0, by decide⟩),
   pushAt 1853 1 96,
   pushAt 1854 2 256,
   opAt 1855 .CALLDATACOPY,
   pushAt 1856 2 2642,
   pushAt 1857 2 512,
   pushAt 1858 2 256,
   pushAt 1859 2 1536,
   pushAt 1860 2 3558,
   opAt 1861 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1862 .JUMPDEST,
   opAt 1863 (.Dup ⟨2, by decide⟩),
   pushAt 1864 1 31,
   opAt 1865 .ADD,
   pushAt 1866 1 5,
   opAt 1867 .SHR,
   opAt 1868 (.Dup ⟨3, by decide⟩),
   opAt 1869 (.Dup ⟨1, by decide⟩),
   pushAt 1870 1 5,
   opAt 1871 .SHL,
   opAt 1872 .SUB,
   pushAt 1873 1 3,
   opAt 1874 .SHL,
   pushAt 1875 1 96,
   opAt 1876 .CALLDATALOAD,
   opAt 1877 (.Swap ⟨0, by decide⟩),
   opAt 1878 .SHR,
   opAt 1879 (.Dup ⟨2, by decide⟩),
   pushAt 1880 1 224,
   opAt 1881 .ADD,
   opAt 1882 .MSTORE,
   pushAt 1883 1 1,
   pushAt 1884 2 967,
   opAt 1885 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
