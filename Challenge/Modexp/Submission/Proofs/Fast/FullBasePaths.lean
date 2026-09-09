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
  [opAt 2455 .JUMPDEST,
   opAt 2456 (.Dup ⟨0, by decide⟩),
   opAt 2457 (.Dup ⟨3, by decide⟩),
   opAt 2458 .EQ,
   pushAt 2459 0 0,
   opAt 2460 .MLOAD,
   pushAt 2461 1 255,
   opAt 2462 .SHR,
   opAt 2463 .AND,
   opAt 2464 .ISZERO,
   pushAt 2465 2 3413,
   opAt 2466 .JUMPI]

/-- pc 3877..3407, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2467 (.Dup ⟨0, by decide⟩),
   pushAt 2468 1 96,
   pushAt 2469 2 1024,
   opAt 2470 .CALLDATACOPY,
   pushAt 2471 2 1746,
   pushAt 2472 2 2048,
   pushAt 2473 2 1024,
   pushAt 2474 2 6144,
   pushAt 2475 2 4453,
   opAt 2476 .JUMP]

/-- pc 3644..3424, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2477 .JUMPDEST,
   pushAt 2478 2 1746,
   pushAt 2479 2 2048,
   pushAt 2480 2 6144,
   pushAt 2481 2 1024,
   pushAt 2482 2 4453,
   opAt 2483 .JUMP]

/-- pc 3425..3458, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2484 .JUMPDEST,
   opAt 2485 (.Dup ⟨2, by decide⟩),
   pushAt 2486 1 31,
   opAt 2487 .ADD,
   pushAt 2488 1 5,
   opAt 2489 .SHR,
   opAt 2490 (.Dup ⟨3, by decide⟩),
   opAt 2491 (.Dup ⟨1, by decide⟩),
   pushAt 2492 1 5,
   opAt 2493 .SHL,
   opAt 2494 .SUB,
   pushAt 2495 1 3,
   opAt 2496 .SHL,
   pushAt 2497 1 96,
   opAt 2498 .CALLDATALOAD,
   opAt 2499 (.Swap ⟨0, by decide⟩),
   opAt 2500 .SHR,
   opAt 2501 (.Dup ⟨2, by decide⟩),
   pushAt 2502 2 992,
   opAt 2503 .ADD,
   opAt 2504 .MSTORE,
   pushAt 2505 1 1,
   pushAt 2506 2 1659,
   opAt 2507 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
