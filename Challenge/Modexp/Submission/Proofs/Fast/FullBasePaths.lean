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
  [opAt 2231 .JUMPDEST,
   opAt 2232 (.Dup ⟨0, by decide⟩),
   opAt 2233 (.Dup ⟨3, by decide⟩),
   opAt 2234 .EQ,
   pushAt 2235 0 0,
   opAt 2236 .MLOAD,
   pushAt 2237 1 255,
   opAt 2238 .SHR,
   opAt 2239 .AND,
   opAt 2240 .ISZERO,
   pushAt 2241 2 2918,
   opAt 2242 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2243 (.Dup ⟨0, by decide⟩),
   pushAt 2244 1 96,
   pushAt 2245 2 1024,
   opAt 2246 .CALLDATACOPY,
   pushAt 2247 2 1481,
   pushAt 2248 2 2048,
   pushAt 2249 2 1024,
   pushAt 2250 2 6144,
   pushAt 2251 2 3862,
   opAt 2252 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2253 .JUMPDEST,
   opAt 2254 (.Dup ⟨2, by decide⟩),
   pushAt 2255 1 31,
   opAt 2256 .ADD,
   pushAt 2257 1 5,
   opAt 2258 .SHR,
   opAt 2259 (.Dup ⟨3, by decide⟩),
   opAt 2260 (.Dup ⟨1, by decide⟩),
   pushAt 2261 1 5,
   opAt 2262 .SHL,
   opAt 2263 .SUB,
   pushAt 2264 1 3,
   opAt 2265 .SHL,
   pushAt 2266 1 96,
   opAt 2267 .CALLDATALOAD,
   opAt 2268 (.Swap ⟨0, by decide⟩),
   opAt 2269 .SHR,
   opAt 2270 (.Dup ⟨2, by decide⟩),
   pushAt 2271 2 992,
   opAt 2272 .ADD,
   opAt 2273 .MSTORE,
   pushAt 2274 1 1,
   pushAt 2275 2 1395,
   opAt 2276 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
