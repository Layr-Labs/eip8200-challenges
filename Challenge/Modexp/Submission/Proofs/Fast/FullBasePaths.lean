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
  [opAt 2356 .JUMPDEST,
   opAt 2357 (.Dup ⟨0, by decide⟩),
   opAt 2358 (.Dup ⟨3, by decide⟩),
   opAt 2359 .EQ,
   pushAt 2360 0 0,
   opAt 2361 .MLOAD,
   pushAt 2362 1 255,
   opAt 2363 .SHR,
   opAt 2364 .AND,
   opAt 2365 .ISZERO,
   pushAt 2366 2 3654,
   opAt 2367 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2368 (.Dup ⟨0, by decide⟩),
   pushAt 2369 1 96,
   pushAt 2370 2 1024,
   opAt 2371 .CALLDATACOPY,
   pushAt 2372 2 3637,
   pushAt 2373 2 1024,
   pushAt 2374 2 3072,
   pushAt 2375 2 1024,
   pushAt 2376 2 2460,
   opAt 2377 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2378 .JUMPDEST,
   pushAt 2379 2 1755,
   pushAt 2380 2 2048,
   pushAt 2381 2 6144,
   pushAt 2382 2 1024,
   pushAt 2383 2 1939,
   opAt 2384 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2385 .JUMPDEST,
   opAt 2386 (.Dup ⟨2, by decide⟩),
   pushAt 2387 1 31,
   opAt 2388 .ADD,
   pushAt 2389 1 5,
   opAt 2390 .SHR,
   opAt 2391 (.Dup ⟨3, by decide⟩),
   opAt 2392 (.Dup ⟨1, by decide⟩),
   pushAt 2393 1 5,
   opAt 2394 .SHL,
   opAt 2395 .SUB,
   pushAt 2396 1 3,
   opAt 2397 .SHL,
   pushAt 2398 1 96,
   opAt 2399 .CALLDATALOAD,
   opAt 2400 (.Swap ⟨0, by decide⟩),
   opAt 2401 .SHR,
   opAt 2402 (.Dup ⟨2, by decide⟩),
   pushAt 2403 2 992,
   opAt 2404 .ADD,
   opAt 2405 .MSTORE,
   pushAt 2406 1 1,
   pushAt 2407 2 1668,
   opAt 2408 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
