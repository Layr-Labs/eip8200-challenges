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
  [opAt 2460 .JUMPDEST,
   opAt 2461 (.Dup ⟨0, by decide⟩),
   opAt 2462 (.Dup ⟨3, by decide⟩),
   opAt 2463 .EQ,
   pushAt 2464 0 0,
   opAt 2465 .MLOAD,
   pushAt 2466 1 255,
   opAt 2467 .SHR,
   opAt 2468 .AND,
   opAt 2469 .ISZERO,
   pushAt 2470 2 3420,
   opAt 2471 .JUMPI]

/-- pc 3877..3407, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2472 (.Dup ⟨0, by decide⟩),
   pushAt 2473 1 96,
   pushAt 2474 2 1024,
   opAt 2475 .CALLDATACOPY,
   pushAt 2476 2 1755,
   pushAt 2477 2 2048,
   pushAt 2478 2 1024,
   pushAt 2479 2 6144,
   pushAt 2480 2 4458,
   opAt 2481 .JUMP]

/-- pc 3644..3424, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2482 .JUMPDEST,
   pushAt 2483 2 1755,
   pushAt 2484 2 2048,
   pushAt 2485 2 6144,
   pushAt 2486 2 1024,
   pushAt 2487 2 4458,
   opAt 2488 .JUMP]

/-- pc 3425..3458, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2489 .JUMPDEST,
   opAt 2490 (.Dup ⟨2, by decide⟩),
   pushAt 2491 1 31,
   opAt 2492 .ADD,
   pushAt 2493 1 5,
   opAt 2494 .SHR,
   opAt 2495 (.Dup ⟨3, by decide⟩),
   opAt 2496 (.Dup ⟨1, by decide⟩),
   pushAt 2497 1 5,
   opAt 2498 .SHL,
   opAt 2499 .SUB,
   pushAt 2500 1 3,
   opAt 2501 .SHL,
   pushAt 2502 1 96,
   opAt 2503 .CALLDATALOAD,
   opAt 2504 (.Swap ⟨0, by decide⟩),
   opAt 2505 .SHR,
   opAt 2506 (.Dup ⟨2, by decide⟩),
   pushAt 2507 2 992,
   opAt 2508 .ADD,
   opAt 2509 .MSTORE,
   pushAt 2510 1 1,
   pushAt 2511 2 1668,
   opAt 2512 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
