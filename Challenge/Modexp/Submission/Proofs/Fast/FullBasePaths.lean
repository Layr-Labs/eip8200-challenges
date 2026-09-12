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
  [opAt 2233 .JUMPDEST,
   opAt 2234 (.Dup ⟨0, by decide⟩),
   opAt 2235 (.Dup ⟨3, by decide⟩),
   opAt 2236 .EQ,
   pushAt 2237 0 0,
   opAt 2238 .MLOAD,
   pushAt 2239 1 255,
   opAt 2240 .SHR,
   opAt 2241 .AND,
   opAt 2242 .ISZERO,
   pushAt 2243 2 2922,
   opAt 2244 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2245 (.Dup ⟨0, by decide⟩),
   pushAt 2246 1 96,
   pushAt 2247 2 1024,
   opAt 2248 .CALLDATACOPY,
   pushAt 2249 2 1481,
   pushAt 2250 2 2048,
   pushAt 2251 2 1024,
   pushAt 2252 2 6144,
   pushAt 2253 2 3901,
   opAt 2254 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2255 .JUMPDEST,
   opAt 2256 (.Dup ⟨2, by decide⟩),
   pushAt 2257 1 31,
   opAt 2258 .ADD,
   pushAt 2259 1 5,
   opAt 2260 .SHR,
   opAt 2261 (.Dup ⟨3, by decide⟩),
   opAt 2262 (.Dup ⟨1, by decide⟩),
   pushAt 2263 1 5,
   opAt 2264 .SHL,
   opAt 2265 .SUB,
   pushAt 2266 1 3,
   opAt 2267 .SHL,
   pushAt 2268 1 96,
   opAt 2269 .CALLDATALOAD,
   opAt 2270 (.Swap ⟨0, by decide⟩),
   opAt 2271 .SHR,
   opAt 2272 (.Dup ⟨2, by decide⟩),
   pushAt 2273 2 992,
   opAt 2274 .ADD,
   opAt 2275 .MSTORE,
   pushAt 2276 1 1,
   pushAt 2277 2 1395,
   opAt 2278 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
