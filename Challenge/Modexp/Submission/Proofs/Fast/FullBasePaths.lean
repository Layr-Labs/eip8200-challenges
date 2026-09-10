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
  [opAt 2439 .JUMPDEST,
   opAt 2440 (.Dup ⟨0, by decide⟩),
   opAt 2441 (.Dup ⟨3, by decide⟩),
   opAt 2442 .EQ,
   pushAt 2443 0 0,
   opAt 2444 .MLOAD,
   pushAt 2445 1 255,
   opAt 2446 .SHR,
   opAt 2447 .AND,
   opAt 2448 .ISZERO,
   pushAt 2449 2 3420,
   opAt 2450 .JUMPI]

/-- pc 3877..3407, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2451 (.Dup ⟨0, by decide⟩),
   pushAt 2452 1 96,
   pushAt 2453 2 1024,
   opAt 2454 .CALLDATACOPY,
   pushAt 2455 2 1755,
   pushAt 2456 2 2048,
   pushAt 2457 2 1024,
   pushAt 2458 2 6144,
   pushAt 2459 2 4465,
   opAt 2460 .JUMP]

/-- pc 3644..3424, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2461 .JUMPDEST,
   pushAt 2462 2 1755,
   pushAt 2463 2 2048,
   pushAt 2464 2 6144,
   pushAt 2465 2 1024,
   pushAt 2466 2 4465,
   opAt 2467 .JUMP]

/-- pc 3425..3458, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2468 .JUMPDEST,
   opAt 2469 (.Dup ⟨2, by decide⟩),
   pushAt 2470 1 31,
   opAt 2471 .ADD,
   pushAt 2472 1 5,
   opAt 2473 .SHR,
   opAt 2474 (.Dup ⟨3, by decide⟩),
   opAt 2475 (.Dup ⟨1, by decide⟩),
   pushAt 2476 1 5,
   opAt 2477 .SHL,
   opAt 2478 .SUB,
   pushAt 2479 1 3,
   opAt 2480 .SHL,
   pushAt 2481 1 96,
   opAt 2482 .CALLDATALOAD,
   opAt 2483 (.Swap ⟨0, by decide⟩),
   opAt 2484 .SHR,
   opAt 2485 (.Dup ⟨2, by decide⟩),
   pushAt 2486 2 992,
   opAt 2487 .ADD,
   opAt 2488 .MSTORE,
   pushAt 2489 1 1,
   pushAt 2490 2 1668,
   opAt 2491 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
