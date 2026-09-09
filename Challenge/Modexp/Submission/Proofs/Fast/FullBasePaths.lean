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
  [opAt 2467 .JUMPDEST,
   opAt 2468 (.Dup ⟨0, by decide⟩),
   opAt 2469 (.Dup ⟨3, by decide⟩),
   opAt 2470 .EQ,
   pushAt 2471 0 0,
   opAt 2472 .MLOAD,
   pushAt 2473 1 255,
   opAt 2474 .SHR,
   opAt 2475 .AND,
   opAt 2476 .ISZERO,
   pushAt 2477 2 3405,
   opAt 2478 .JUMPI]

/-- pc 3877..3407, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2479 (.Dup ⟨0, by decide⟩),
   pushAt 2480 1 96,
   pushAt 2481 2 1024,
   opAt 2482 .CALLDATACOPY,
   pushAt 2483 2 1755,
   pushAt 2484 2 2048,
   pushAt 2485 2 1024,
   pushAt 2486 2 6144,
   pushAt 2487 2 4458,
   opAt 2488 .JUMP]

/-- pc 3644..3424, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2489 .JUMPDEST,
   pushAt 2490 2 1755,
   pushAt 2491 2 2048,
   pushAt 2492 2 6144,
   pushAt 2493 2 1024,
   pushAt 2494 2 4458,
   opAt 2495 .JUMP]

/-- pc 3425..3458, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2496 .JUMPDEST,
   opAt 2497 (.Dup ⟨2, by decide⟩),
   pushAt 2498 1 31,
   opAt 2499 .ADD,
   pushAt 2500 1 5,
   opAt 2501 .SHR,
   opAt 2502 (.Dup ⟨3, by decide⟩),
   opAt 2503 (.Dup ⟨1, by decide⟩),
   pushAt 2504 1 5,
   opAt 2505 .SHL,
   opAt 2506 .SUB,
   pushAt 2507 1 3,
   opAt 2508 .SHL,
   pushAt 2509 1 96,
   opAt 2510 .CALLDATALOAD,
   opAt 2511 (.Swap ⟨0, by decide⟩),
   opAt 2512 .SHR,
   opAt 2513 (.Dup ⟨2, by decide⟩),
   pushAt 2514 2 992,
   opAt 2515 .ADD,
   opAt 2516 .MSTORE,
   pushAt 2517 1 1,
   pushAt 2518 2 1668,
   opAt 2519 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
