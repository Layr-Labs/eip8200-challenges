import Challenge.Modexp.Submission.Proofs.Fast.Paths.P4
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located paths for the full-width-base helper

The helper is appended after the fixed-window and direct-RR helpers. Its miss
path reproduces the original base-head computation before jumping to the
unchanged base loop at pc 1668.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2124 .JUMPDEST,
   opAt 2125 (.Dup ⟨0, by decide⟩),
   opAt 2126 (.Dup ⟨3, by decide⟩),
   opAt 2127 .EQ,
   pushAt 2128 0 0,
   opAt 2129 .MLOAD,
   pushAt 2130 1 255,
   opAt 2131 .SHR,
   opAt 2132 .AND,
   opAt 2133 .ISZERO,
   pushAt 2134 2 2777,
   opAt 2135 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2136 (.Dup ⟨0, by decide⟩),
   pushAt 2137 1 96,
   pushAt 2138 2 1024,
   opAt 2139 .CALLDATACOPY,
   pushAt 2140 2 1336,
   pushAt 2141 2 2048,
   pushAt 2142 2 1024,
   pushAt 2143 2 6144,
   pushAt 2144 2 3779,
   opAt 2145 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2146 .JUMPDEST,
   opAt 2147 (.Dup ⟨2, by decide⟩),
   pushAt 2148 1 31,
   opAt 2149 .ADD,
   pushAt 2150 1 5,
   opAt 2151 .SHR,
   opAt 2152 (.Dup ⟨3, by decide⟩),
   opAt 2153 (.Dup ⟨1, by decide⟩),
   pushAt 2154 1 5,
   opAt 2155 .SHL,
   opAt 2156 .SUB,
   pushAt 2157 1 3,
   opAt 2158 .SHL,
   pushAt 2159 1 96,
   opAt 2160 .CALLDATALOAD,
   opAt 2161 (.Swap ⟨0, by decide⟩),
   opAt 2162 .SHR,
   opAt 2163 (.Dup ⟨2, by decide⟩),
   pushAt 2164 2 992,
   opAt 2165 .ADD,
   opAt 2166 .MSTORE,
   pushAt 2167 1 1,
   pushAt 2168 2 1250,
   opAt 2169 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
