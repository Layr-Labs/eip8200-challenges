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
  [opAt 1837 .JUMPDEST,
   opAt 1838 (.Dup ⟨0, by decide⟩),
   opAt 1839 (.Dup ⟨3, by decide⟩),
   opAt 1840 .EQ,
   pushAt 1841 0 0,
   opAt 1842 .MLOAD,
   pushAt 1843 1 255,
   opAt 1844 .SHR,
   opAt 1845 .AND,
   opAt 1846 .ISZERO,
   pushAt 1847 2 2467,
   opAt 1848 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1849 (.Dup ⟨0, by decide⟩),
   pushAt 1850 1 96,
   pushAt 1851 2 256,
   opAt 1852 .CALLDATACOPY,
   pushAt 1853 2 2637,
   pushAt 1854 2 512,
   pushAt 1855 2 256,
   pushAt 1856 2 1536,
   pushAt 1857 2 3550,
   opAt 1858 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1859 .JUMPDEST,
   opAt 1860 (.Dup ⟨2, by decide⟩),
   pushAt 1861 1 31,
   opAt 1862 .ADD,
   pushAt 1863 1 5,
   opAt 1864 .SHR,
   opAt 1865 (.Dup ⟨3, by decide⟩),
   opAt 1866 (.Dup ⟨1, by decide⟩),
   pushAt 1867 1 5,
   opAt 1868 .SHL,
   opAt 1869 .SUB,
   pushAt 1870 1 3,
   opAt 1871 .SHL,
   pushAt 1872 1 96,
   opAt 1873 .CALLDATALOAD,
   opAt 1874 (.Swap ⟨0, by decide⟩),
   opAt 1875 .SHR,
   opAt 1876 (.Dup ⟨2, by decide⟩),
   pushAt 1877 1 224,
   opAt 1878 .ADD,
   opAt 1879 .MSTORE,
   pushAt 1880 1 1,
   pushAt 1881 2 962,
   opAt 1882 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
