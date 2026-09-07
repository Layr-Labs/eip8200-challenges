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

/-- pc 3606..3620, indices 2361..2372: size/top-bit guard. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2253 .JUMPDEST,
   opAt 2254 (.Dup ⟨0, by decide⟩),
   opAt 2255 (.Dup ⟨3, by decide⟩),
   opAt 2256 .EQ,
   pushAt 2257 0 0,
   opAt 2258 .MLOAD,
   pushAt 2259 1 255,
   opAt 2260 .SHR,
   opAt 2261 .AND,
   opAt 2262 .ISZERO,
   pushAt 2263 2 3656,
   opAt 2264 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2265 (.Dup ⟨0, by decide⟩),
   pushAt 2266 1 96,
   pushAt 2267 2 1024,
   opAt 2268 .CALLDATACOPY,
   pushAt 2269 2 1755,
   pushAt 2270 2 2048,
   pushAt 2271 2 1024,
   pushAt 2272 2 6144,
   pushAt 2273 2 1939,
   opAt 2274 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2275 .JUMPDEST,
   pushAt 2276 2 1755,
   pushAt 2277 2 2048,
   pushAt 2278 2 6144,
   pushAt 2279 2 1024,
   pushAt 2280 2 1939,
   opAt 2281 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2282 .JUMPDEST,
   opAt 2283 (.Dup ⟨2, by decide⟩),
   pushAt 2284 1 31,
   opAt 2285 .ADD,
   pushAt 2286 1 5,
   opAt 2287 .SHR,
   opAt 2288 (.Dup ⟨3, by decide⟩),
   opAt 2289 (.Dup ⟨1, by decide⟩),
   pushAt 2290 1 5,
   opAt 2291 .SHL,
   opAt 2292 .SUB,
   pushAt 2293 1 3,
   opAt 2294 .SHL,
   pushAt 2295 1 96,
   opAt 2296 .CALLDATALOAD,
   opAt 2297 (.Swap ⟨0, by decide⟩),
   opAt 2298 .SHR,
   opAt 2299 (.Dup ⟨2, by decide⟩),
   pushAt 2300 2 992,
   opAt 2301 .ADD,
   opAt 2302 .MSTORE,
   pushAt 2303 1 1,
   pushAt 2304 2 1668,
   opAt 2305 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
