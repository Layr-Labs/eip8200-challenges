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
  [opAt 2279 .JUMPDEST,
   opAt 2280 (.Dup ⟨0, by decide⟩),
   opAt 2281 (.Dup ⟨3, by decide⟩),
   opAt 2282 .EQ,
   pushAt 2283 0 0,
   opAt 2284 .MLOAD,
   pushAt 2285 1 255,
   opAt 2286 .SHR,
   opAt 2287 .AND,
   opAt 2288 .ISZERO,
   pushAt 2289 2 3661,
   opAt 2290 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2291 (.Dup ⟨0, by decide⟩),
   pushAt 2292 1 96,
   pushAt 2293 2 1024,
   opAt 2294 .CALLDATACOPY,
   pushAt 2295 2 1755,
   pushAt 2296 2 2048,
   pushAt 2297 2 1024,
   pushAt 2298 2 6144,
   pushAt 2299 2 1939,
   opAt 2300 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2301 .JUMPDEST,
   pushAt 2302 2 1755,
   pushAt 2303 2 2048,
   pushAt 2304 2 6144,
   pushAt 2305 2 1024,
   pushAt 2306 2 1939,
   opAt 2307 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2308 .JUMPDEST,
   opAt 2309 (.Dup ⟨2, by decide⟩),
   pushAt 2310 1 31,
   opAt 2311 .ADD,
   pushAt 2312 1 5,
   opAt 2313 .SHR,
   opAt 2314 (.Dup ⟨3, by decide⟩),
   opAt 2315 (.Dup ⟨1, by decide⟩),
   pushAt 2316 1 5,
   opAt 2317 .SHL,
   opAt 2318 .SUB,
   pushAt 2319 1 3,
   opAt 2320 .SHL,
   pushAt 2321 1 96,
   opAt 2322 .CALLDATALOAD,
   opAt 2323 (.Swap ⟨0, by decide⟩),
   opAt 2324 .SHR,
   opAt 2325 (.Dup ⟨2, by decide⟩),
   pushAt 2326 2 992,
   opAt 2327 .ADD,
   opAt 2328 .MSTORE,
   pushAt 2329 1 1,
   pushAt 2330 2 1668,
   opAt 2331 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
