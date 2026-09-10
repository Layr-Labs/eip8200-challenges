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
  [opAt 2459 .JUMPDEST,
   opAt 2460 (.Dup ⟨0, by decide⟩),
   opAt 2461 (.Dup ⟨3, by decide⟩),
   opAt 2462 .EQ,
   pushAt 2463 0 0,
   opAt 2464 .MLOAD,
   pushAt 2465 1 255,
   opAt 2466 .SHR,
   opAt 2467 .AND,
   opAt 2468 .ISZERO,
   pushAt 2469 2 3420,
   opAt 2470 .JUMPI]

/-- pc 3877..3407, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2471 (.Dup ⟨0, by decide⟩),
   pushAt 2472 1 96,
   pushAt 2473 2 1024,
   opAt 2474 .CALLDATACOPY,
   pushAt 2475 2 1755,
   pushAt 2476 2 2048,
   pushAt 2477 2 1024,
   pushAt 2478 2 6144,
   pushAt 2479 2 4465,
   opAt 2480 .JUMP]

/-- pc 3644..3424, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2481 .JUMPDEST,
   pushAt 2482 2 1755,
   pushAt 2483 2 2048,
   pushAt 2484 2 6144,
   pushAt 2485 2 1024,
   pushAt 2486 2 4465,
   opAt 2487 .JUMP]

/-- pc 3425..3458, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2488 .JUMPDEST,
   opAt 2489 (.Dup ⟨2, by decide⟩),
   pushAt 2490 1 31,
   opAt 2491 .ADD,
   pushAt 2492 1 5,
   opAt 2493 .SHR,
   opAt 2494 (.Dup ⟨3, by decide⟩),
   opAt 2495 (.Dup ⟨1, by decide⟩),
   pushAt 2496 1 5,
   opAt 2497 .SHL,
   opAt 2498 .SUB,
   pushAt 2499 1 3,
   opAt 2500 .SHL,
   pushAt 2501 1 96,
   opAt 2502 .CALLDATALOAD,
   opAt 2503 (.Swap ⟨0, by decide⟩),
   opAt 2504 .SHR,
   opAt 2505 (.Dup ⟨2, by decide⟩),
   pushAt 2506 2 992,
   opAt 2507 .ADD,
   opAt 2508 .MSTORE,
   pushAt 2509 1 1,
   pushAt 2510 2 1668,
   opAt 2511 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
