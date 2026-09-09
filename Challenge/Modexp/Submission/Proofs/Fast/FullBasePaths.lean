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
  [opAt 2456 .JUMPDEST,
   opAt 2457 (.Dup ⟨0, by decide⟩),
   opAt 2458 (.Dup ⟨3, by decide⟩),
   opAt 2459 .EQ,
   pushAt 2460 0 0,
   opAt 2461 .MLOAD,
   pushAt 2462 1 255,
   opAt 2463 .SHR,
   opAt 2464 .AND,
   opAt 2465 .ISZERO,
   pushAt 2466 2 3384,
   opAt 2467 .JUMPI]

/-- pc 3877..3407, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2468 (.Dup ⟨0, by decide⟩),
   pushAt 2469 1 96,
   pushAt 2470 2 1024,
   opAt 2471 .CALLDATACOPY,
   pushAt 2472 2 1746,
   pushAt 2473 2 2048,
   pushAt 2474 2 1024,
   pushAt 2475 2 6144,
   pushAt 2476 2 4424,
   opAt 2477 .JUMP]

/-- pc 3644..3424, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2478 .JUMPDEST,
   pushAt 2479 2 1746,
   pushAt 2480 2 2048,
   pushAt 2481 2 6144,
   pushAt 2482 2 1024,
   pushAt 2483 2 4424,
   opAt 2484 .JUMP]

/-- pc 3425..3458, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2485 .JUMPDEST,
   opAt 2486 (.Dup ⟨2, by decide⟩),
   pushAt 2487 1 31,
   opAt 2488 .ADD,
   pushAt 2489 1 5,
   opAt 2490 .SHR,
   opAt 2491 (.Dup ⟨3, by decide⟩),
   opAt 2492 (.Dup ⟨1, by decide⟩),
   pushAt 2493 1 5,
   opAt 2494 .SHL,
   opAt 2495 .SUB,
   pushAt 2496 1 3,
   opAt 2497 .SHL,
   pushAt 2498 1 96,
   opAt 2499 .CALLDATALOAD,
   opAt 2500 (.Swap ⟨0, by decide⟩),
   opAt 2501 .SHR,
   opAt 2502 (.Dup ⟨2, by decide⟩),
   pushAt 2503 2 992,
   opAt 2504 .ADD,
   opAt 2505 .MSTORE,
   pushAt 2506 1 1,
   pushAt 2507 2 1659,
   opAt 2508 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
