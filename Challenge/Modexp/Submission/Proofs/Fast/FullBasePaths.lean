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
  [opAt 1838 .JUMPDEST,
   opAt 1839 (.Dup ⟨0, by decide⟩),
   opAt 1840 (.Dup ⟨3, by decide⟩),
   opAt 1841 .EQ,
   pushAt 1842 0 0,
   opAt 1843 .MLOAD,
   pushAt 1844 1 255,
   opAt 1845 .SHR,
   opAt 1846 .AND,
   opAt 1847 .ISZERO,
   pushAt 1848 2 2468,
   opAt 1849 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1850 (.Dup ⟨0, by decide⟩),
   pushAt 1851 1 96,
   pushAt 1852 2 256,
   opAt 1853 .CALLDATACOPY,
   pushAt 1854 2 2638,
   pushAt 1855 2 512,
   pushAt 1856 2 256,
   pushAt 1857 2 1536,
   pushAt 1858 2 3550,
   opAt 1859 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1860 .JUMPDEST,
   opAt 1861 (.Dup ⟨2, by decide⟩),
   pushAt 1862 1 31,
   opAt 1863 .ADD,
   pushAt 1864 1 5,
   opAt 1865 .SHR,
   opAt 1866 (.Dup ⟨3, by decide⟩),
   opAt 1867 (.Dup ⟨1, by decide⟩),
   pushAt 1868 1 5,
   opAt 1869 .SHL,
   opAt 1870 .SUB,
   pushAt 1871 1 3,
   opAt 1872 .SHL,
   pushAt 1873 1 96,
   opAt 1874 .CALLDATALOAD,
   opAt 1875 (.Swap ⟨0, by decide⟩),
   opAt 1876 .SHR,
   opAt 1877 (.Dup ⟨2, by decide⟩),
   pushAt 1878 1 224,
   opAt 1879 .ADD,
   opAt 1880 .MSTORE,
   pushAt 1881 1 1,
   pushAt 1882 2 963,
   opAt 1883 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
