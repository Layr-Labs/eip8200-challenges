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
  [opAt 1847 .JUMPDEST,
   opAt 1848 (.Dup ⟨0, by decide⟩),
   opAt 1849 (.Dup ⟨3, by decide⟩),
   opAt 1850 .EQ,
   pushAt 1851 0 0,
   opAt 1852 .MLOAD,
   pushAt 1853 1 255,
   opAt 1854 .SHR,
   opAt 1855 .AND,
   opAt 1856 .ISZERO,
   pushAt 1857 2 2511,
   opAt 1858 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1859 (.Dup ⟨0, by decide⟩),
   pushAt 1860 1 96,
   pushAt 1861 2 256,
   opAt 1862 .CALLDATACOPY,
   pushAt 1863 2 2682,
   pushAt 1864 2 512,
   pushAt 1865 2 256,
   pushAt 1866 2 1536,
   pushAt 1867 2 3552,
   opAt 1868 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1869 .JUMPDEST,
   opAt 1870 (.Dup ⟨2, by decide⟩),
   pushAt 1871 1 31,
   opAt 1872 .ADD,
   pushAt 1873 1 5,
   opAt 1874 .SHR,
   opAt 1875 (.Dup ⟨3, by decide⟩),
   opAt 1876 (.Dup ⟨1, by decide⟩),
   pushAt 1877 1 5,
   opAt 1878 .SHL,
   opAt 1879 .SUB,
   pushAt 1880 1 3,
   opAt 1881 .SHL,
   pushAt 1882 1 96,
   opAt 1883 .CALLDATALOAD,
   opAt 1884 (.Swap ⟨0, by decide⟩),
   opAt 1885 .SHR,
   opAt 1886 (.Dup ⟨2, by decide⟩),
   pushAt 1887 1 224,
   opAt 1888 .ADD,
   opAt 1889 .MSTORE,
   pushAt 1890 1 1,
   pushAt 1891 2 979,
   opAt 1892 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
