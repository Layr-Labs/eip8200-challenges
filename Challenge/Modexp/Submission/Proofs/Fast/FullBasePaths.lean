import Challenge.Modexp.Submission.Proofs.Fast.Paths.P4
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located paths for the full-width-base helper

The helper is appended after the fixed-window and direct-RR helpers. Its miss
path reproduces the original base-head computation before jumping to the
unchanged base loop at pc 1716.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2258 .JUMPDEST,
   opAt 2259 (.Dup ⟨0, by decide⟩),
   opAt 2260 (.Dup ⟨3, by decide⟩),
   opAt 2261 .EQ,
   pushAt 2262 0 0,
   opAt 2263 .MLOAD,
   pushAt 2264 1 255,
   opAt 2265 .SHR,
   opAt 2266 .AND,
   opAt 2267 .ISZERO,
   pushAt 2268 2 2951,
   opAt 2269 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2270 (.Dup ⟨0, by decide⟩),
   pushAt 2271 1 96,
   pushAt 2272 2 1024,
   opAt 2273 .CALLDATACOPY,
   pushAt 2274 2 1517,
   pushAt 2275 2 2048,
   pushAt 2276 2 1024,
   pushAt 2277 2 6144,
   pushAt 2278 2 4055,
   opAt 2279 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2280 .JUMPDEST,
   opAt 2281 (.Dup ⟨2, by decide⟩),
   pushAt 2282 1 31,
   opAt 2283 .ADD,
   pushAt 2284 1 5,
   opAt 2285 .SHR,
   opAt 2286 (.Dup ⟨3, by decide⟩),
   opAt 2287 (.Dup ⟨1, by decide⟩),
   pushAt 2288 1 5,
   opAt 2289 .SHL,
   opAt 2290 .SUB,
   pushAt 2291 1 3,
   opAt 2292 .SHL,
   pushAt 2293 1 96,
   opAt 2294 .CALLDATALOAD,
   opAt 2295 (.Swap ⟨0, by decide⟩),
   opAt 2296 .SHR,
   opAt 2297 (.Dup ⟨2, by decide⟩),
   pushAt 2298 2 992,
   opAt 2299 .ADD,
   opAt 2300 .MSTORE,
   pushAt 2301 1 1,
   pushAt 2302 2 1431,
   opAt 2303 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
