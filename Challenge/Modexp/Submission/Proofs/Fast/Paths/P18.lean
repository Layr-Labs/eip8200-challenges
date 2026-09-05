import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Guarded two-limb residue path (group 18)

These four blocks cover the appended exact-case guard and its direct return.
Each failed comparison transfers to the original `DOUBLE256` entry with the
incoming stack and memory intact.  The successful path replaces the two words
at `R1` and returns through the incoming continuation.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1883..1890, pc 3086..3098: require `V_N = 2`. -/
def blk1883 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1883 .JUMPDEST,
   pushAt 1884 2 9504,
   opAt 1885 .MLOAD,
   pushAt 1886 1 2,
   opAt 1887 .EQ,
   opAt 1888 .ISZERO,
   pushAt 1889 2 1911,
   opAt 1890 .JUMPI]

/-- Instructions 1891..1897, pc 3099..3108: require the high modulus word to be one. -/
def blk1891 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1891 0 0,
   opAt 1892 .MLOAD,
   pushAt 1893 1 1,
   opAt 1894 .EQ,
   opAt 1895 .ISZERO,
   pushAt 1896 2 1911,
   opAt 1897 .JUMPI]

/-- Instructions 1898..1904, pc 3109..3119: require the low modulus word to be seven. -/
def blk1898 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1898 1 32,
   opAt 1899 .MLOAD,
   pushAt 1900 1 7,
   opAt 1901 .EQ,
   opAt 1902 .ISZERO,
   pushAt 1903 2 1911,
   opAt 1904 .JUMPI]

/-- Instructions 1905..1912, pc 3120..3132: write `[0, 49]`, discard the
destination pointer and return through the incoming continuation. -/
def blk1905 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1905 0 0,
   pushAt 1906 2 4096,
   opAt 1907 .MSTORE,
   pushAt 1908 1 49,
   pushAt 1909 2 4128,
   opAt 1910 .MSTORE,
   opAt 1911 .POP,
   opAt 1912 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
