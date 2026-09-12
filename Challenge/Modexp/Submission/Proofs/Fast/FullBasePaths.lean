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
  [opAt 2252 .JUMPDEST,
   opAt 2253 (.Dup ⟨0, by decide⟩),
   opAt 2254 (.Dup ⟨3, by decide⟩),
   opAt 2255 .EQ,
   pushAt 2256 0 0,
   opAt 2257 .MLOAD,
   pushAt 2258 1 255,
   opAt 2259 .SHR,
   opAt 2260 .AND,
   opAt 2261 .ISZERO,
   pushAt 2262 2 2951,
   opAt 2263 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2264 (.Dup ⟨0, by decide⟩),
   pushAt 2265 1 96,
   pushAt 2266 2 256,
   opAt 2267 .CALLDATACOPY,
   pushAt 2268 2 1502,
   pushAt 2269 2 512,
   pushAt 2270 2 256,
   pushAt 2271 2 1536,
   pushAt 2272 2 3920,
   opAt 2273 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2274 .JUMPDEST,
   opAt 2275 (.Dup ⟨2, by decide⟩),
   pushAt 2276 1 31,
   opAt 2277 .ADD,
   pushAt 2278 1 5,
   opAt 2279 .SHR,
   opAt 2280 (.Dup ⟨3, by decide⟩),
   opAt 2281 (.Dup ⟨1, by decide⟩),
   pushAt 2282 1 5,
   opAt 2283 .SHL,
   opAt 2284 .SUB,
   pushAt 2285 1 3,
   opAt 2286 .SHL,
   pushAt 2287 1 96,
   opAt 2288 .CALLDATALOAD,
   opAt 2289 (.Swap ⟨0, by decide⟩),
   opAt 2290 .SHR,
   opAt 2291 (.Dup ⟨2, by decide⟩),
   pushAt 2292 2 224,
   opAt 2293 .ADD,
   opAt 2294 .MSTORE,
   pushAt 2295 1 1,
   pushAt 2296 2 1416,
   opAt 2297 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
