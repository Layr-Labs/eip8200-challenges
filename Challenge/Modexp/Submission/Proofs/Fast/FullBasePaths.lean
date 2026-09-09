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
  [opAt 2458 .JUMPDEST,
   opAt 2459 (.Dup ⟨0, by decide⟩),
   opAt 2460 (.Dup ⟨3, by decide⟩),
   opAt 2461 .EQ,
   pushAt 2462 0 0,
   opAt 2463 .MLOAD,
   pushAt 2464 1 255,
   opAt 2465 .SHR,
   opAt 2466 .AND,
   opAt 2467 .ISZERO,
   pushAt 2468 2 3384,
   opAt 2469 .JUMPI]

/-- pc 3877..3407, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2470 (.Dup ⟨0, by decide⟩),
   pushAt 2471 1 96,
   pushAt 2472 2 1024,
   opAt 2473 .CALLDATACOPY,
   pushAt 2474 2 1746,
   pushAt 2475 2 2048,
   pushAt 2476 2 1024,
   pushAt 2477 2 6144,
   pushAt 2478 2 4424,
   opAt 2479 .JUMP]

/-- pc 3644..3424, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2480 .JUMPDEST,
   pushAt 2481 2 1746,
   pushAt 2482 2 2048,
   pushAt 2483 2 6144,
   pushAt 2484 2 1024,
   pushAt 2485 2 4424,
   opAt 2486 .JUMP]

/-- pc 3425..3458, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2487 .JUMPDEST,
   opAt 2488 (.Dup ⟨2, by decide⟩),
   pushAt 2489 1 31,
   opAt 2490 .ADD,
   pushAt 2491 1 5,
   opAt 2492 .SHR,
   opAt 2493 (.Dup ⟨3, by decide⟩),
   opAt 2494 (.Dup ⟨1, by decide⟩),
   pushAt 2495 1 5,
   opAt 2496 .SHL,
   opAt 2497 .SUB,
   pushAt 2498 1 3,
   opAt 2499 .SHL,
   pushAt 2500 1 96,
   opAt 2501 .CALLDATALOAD,
   opAt 2502 (.Swap ⟨0, by decide⟩),
   opAt 2503 .SHR,
   opAt 2504 (.Dup ⟨2, by decide⟩),
   pushAt 2505 2 992,
   opAt 2506 .ADD,
   opAt 2507 .MSTORE,
   pushAt 2508 1 1,
   pushAt 2509 2 1659,
   opAt 2510 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
