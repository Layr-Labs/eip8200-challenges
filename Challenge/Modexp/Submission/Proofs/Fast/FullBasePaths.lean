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

/-- pc 3370..3876, indices 2361..2372: size/top-bit guard. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2447 .JUMPDEST,
   opAt 2448 (.Dup ⟨0, by decide⟩),
   opAt 2449 (.Dup ⟨3, by decide⟩),
   opAt 2450 .EQ,
   pushAt 2451 0 0,
   opAt 2452 .MLOAD,
   pushAt 2453 1 255,
   opAt 2454 .SHR,
   opAt 2455 .AND,
   opAt 2456 .ISZERO,
   pushAt 2457 2 3420,
   opAt 2458 .JUMPI]

/-- pc 3877..3407, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2459 (.Dup ⟨0, by decide⟩),
   pushAt 2460 1 96,
   pushAt 2461 2 1024,
   opAt 2462 .CALLDATACOPY,
   pushAt 2463 2 1755,
   pushAt 2464 2 2048,
   pushAt 2465 2 1024,
   pushAt 2466 2 6144,
   pushAt 2467 2 4458,
   opAt 2468 .JUMP]

/-- pc 3644..3424, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2469 .JUMPDEST,
   pushAt 2470 2 1755,
   pushAt 2471 2 2048,
   pushAt 2472 2 6144,
   pushAt 2473 2 1024,
   pushAt 2474 2 4458,
   opAt 2475 .JUMP]

/-- pc 3425..3458, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2476 .JUMPDEST,
   opAt 2477 (.Dup ⟨2, by decide⟩),
   pushAt 2478 1 31,
   opAt 2479 .ADD,
   pushAt 2480 1 5,
   opAt 2481 .SHR,
   opAt 2482 (.Dup ⟨3, by decide⟩),
   opAt 2483 (.Dup ⟨1, by decide⟩),
   pushAt 2484 1 5,
   opAt 2485 .SHL,
   opAt 2486 .SUB,
   pushAt 2487 1 3,
   opAt 2488 .SHL,
   pushAt 2489 1 96,
   opAt 2490 .CALLDATALOAD,
   opAt 2491 (.Swap ⟨0, by decide⟩),
   opAt 2492 .SHR,
   opAt 2493 (.Dup ⟨2, by decide⟩),
   pushAt 2494 2 992,
   opAt 2495 .ADD,
   opAt 2496 .MSTORE,
   pushAt 2497 1 1,
   pushAt 2498 2 1668,
   opAt 2499 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
