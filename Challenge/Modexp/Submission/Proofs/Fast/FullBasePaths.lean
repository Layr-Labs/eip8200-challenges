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
  [opAt 2274 .JUMPDEST,
   opAt 2275 (.Dup ⟨0, by decide⟩),
   opAt 2276 (.Dup ⟨3, by decide⟩),
   opAt 2277 .EQ,
   pushAt 2278 0 0,
   opAt 2279 .MLOAD,
   pushAt 2280 1 255,
   opAt 2281 .SHR,
   opAt 2282 .AND,
   opAt 2283 .ISZERO,
   pushAt 2284 2 3661,
   opAt 2285 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2286 (.Dup ⟨0, by decide⟩),
   pushAt 2287 1 96,
   pushAt 2288 2 1024,
   opAt 2289 .CALLDATACOPY,
   pushAt 2290 2 1755,
   pushAt 2291 2 2048,
   pushAt 2292 2 1024,
   pushAt 2293 2 6144,
   pushAt 2294 2 1939,
   opAt 2295 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2296 .JUMPDEST,
   pushAt 2297 2 1755,
   pushAt 2298 2 2048,
   pushAt 2299 2 6144,
   pushAt 2300 2 1024,
   pushAt 2301 2 1939,
   opAt 2302 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2303 .JUMPDEST,
   opAt 2304 (.Dup ⟨2, by decide⟩),
   pushAt 2305 1 31,
   opAt 2306 .ADD,
   pushAt 2307 1 5,
   opAt 2308 .SHR,
   opAt 2309 (.Dup ⟨3, by decide⟩),
   opAt 2310 (.Dup ⟨1, by decide⟩),
   pushAt 2311 1 5,
   opAt 2312 .SHL,
   opAt 2313 .SUB,
   pushAt 2314 1 3,
   opAt 2315 .SHL,
   pushAt 2316 1 96,
   opAt 2317 .CALLDATALOAD,
   opAt 2318 (.Swap ⟨0, by decide⟩),
   opAt 2319 .SHR,
   opAt 2320 (.Dup ⟨2, by decide⟩),
   pushAt 2321 2 992,
   opAt 2322 .ADD,
   opAt 2323 .MSTORE,
   pushAt 2324 1 1,
   pushAt 2325 2 1668,
   opAt 2326 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
