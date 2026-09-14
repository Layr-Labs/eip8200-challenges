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
  [opAt 1839 .JUMPDEST,
   opAt 1840 (.Dup ⟨0, by decide⟩),
   opAt 1841 (.Dup ⟨3, by decide⟩),
   opAt 1842 .EQ,
   pushAt 1843 0 0,
   opAt 1844 .MLOAD,
   pushAt 1845 1 255,
   opAt 1846 .SHR,
   opAt 1847 .AND,
   opAt 1848 .ISZERO,
   pushAt 1849 2 2467,
   opAt 1850 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1851 (.Dup ⟨0, by decide⟩),
   pushAt 1852 1 96,
   pushAt 1853 2 256,
   opAt 1854 .CALLDATACOPY,
   pushAt 1855 2 2637,
   pushAt 1856 2 512,
   pushAt 1857 2 256,
   pushAt 1858 2 1536,
   pushAt 1859 2 3550,
   opAt 1860 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1861 .JUMPDEST,
   opAt 1862 (.Dup ⟨2, by decide⟩),
   pushAt 1863 1 31,
   opAt 1864 .ADD,
   pushAt 1865 1 5,
   opAt 1866 .SHR,
   opAt 1867 (.Dup ⟨3, by decide⟩),
   opAt 1868 (.Dup ⟨1, by decide⟩),
   pushAt 1869 1 5,
   opAt 1870 .SHL,
   opAt 1871 .SUB,
   pushAt 1872 1 3,
   opAt 1873 .SHL,
   pushAt 1874 1 96,
   opAt 1875 .CALLDATALOAD,
   opAt 1876 (.Swap ⟨0, by decide⟩),
   opAt 1877 .SHR,
   opAt 1878 (.Dup ⟨2, by decide⟩),
   pushAt 1879 1 224,
   opAt 1880 .ADD,
   opAt 1881 .MSTORE,
   pushAt 1882 1 1,
   pushAt 1883 2 963,
   opAt 1884 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
