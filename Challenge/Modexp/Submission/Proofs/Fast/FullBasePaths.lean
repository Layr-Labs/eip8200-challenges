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
  [opAt 2263 .JUMPDEST,
   opAt 2264 (.Dup ⟨0, by decide⟩),
   opAt 2265 (.Dup ⟨3, by decide⟩),
   opAt 2266 .EQ,
   pushAt 2267 0 0,
   opAt 2268 .MLOAD,
   pushAt 2269 1 255,
   opAt 2270 .SHR,
   opAt 2271 .AND,
   opAt 2272 .ISZERO,
   pushAt 2273 2 3579,
   opAt 2274 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2275 (.Dup ⟨0, by decide⟩),
   pushAt 2276 1 96,
   pushAt 2277 2 1024,
   opAt 2278 .CALLDATACOPY,
   pushAt 2279 2 1755,
   pushAt 2280 2 2048,
   pushAt 2281 2 1024,
   pushAt 2282 2 6144,
   pushAt 2283 2 1939,
   opAt 2284 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2285 .JUMPDEST,
   pushAt 2286 2 1755,
   pushAt 2287 2 2048,
   pushAt 2288 2 6144,
   pushAt 2289 2 1024,
   pushAt 2290 2 1939,
   opAt 2291 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2292 .JUMPDEST,
   opAt 2293 (.Dup ⟨2, by decide⟩),
   pushAt 2294 1 31,
   opAt 2295 .ADD,
   pushAt 2296 1 5,
   opAt 2297 .SHR,
   opAt 2298 (.Dup ⟨3, by decide⟩),
   opAt 2299 (.Dup ⟨1, by decide⟩),
   pushAt 2300 1 5,
   opAt 2301 .SHL,
   opAt 2302 .SUB,
   pushAt 2303 1 3,
   opAt 2304 .SHL,
   pushAt 2305 1 96,
   opAt 2306 .CALLDATALOAD,
   opAt 2307 (.Swap ⟨0, by decide⟩),
   opAt 2308 .SHR,
   opAt 2309 (.Dup ⟨2, by decide⟩),
   pushAt 2310 2 992,
   opAt 2311 .ADD,
   opAt 2312 .MSTORE,
   pushAt 2313 1 1,
   pushAt 2314 2 1668,
   opAt 2315 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
