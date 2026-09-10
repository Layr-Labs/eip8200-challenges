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
  [opAt 2466 .JUMPDEST,
   opAt 2467 (.Dup ⟨0, by decide⟩),
   opAt 2468 (.Dup ⟨3, by decide⟩),
   opAt 2469 .EQ,
   pushAt 2470 0 0,
   opAt 2471 .MLOAD,
   pushAt 2472 1 255,
   opAt 2473 .SHR,
   opAt 2474 .AND,
   opAt 2475 .ISZERO,
   pushAt 2476 2 3404,
   opAt 2477 .JUMPI]

/-- pc 3877..3407, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2478 (.Dup ⟨0, by decide⟩),
   pushAt 2479 1 96,
   pushAt 2480 2 1024,
   opAt 2481 .CALLDATACOPY,
   pushAt 2482 2 1736,
   pushAt 2483 2 2048,
   pushAt 2484 2 1024,
   pushAt 2485 2 6144,
   pushAt 2486 2 4440,
   opAt 2487 .JUMP]

/-- pc 3644..3424, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2488 .JUMPDEST,
   pushAt 2489 2 1736,
   pushAt 2490 2 2048,
   pushAt 2491 2 6144,
   pushAt 2492 2 1024,
   pushAt 2493 2 4440,
   opAt 2494 .JUMP]

/-- pc 3425..3458, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2495 .JUMPDEST,
   opAt 2496 (.Dup ⟨2, by decide⟩),
   pushAt 2497 1 31,
   opAt 2498 .ADD,
   pushAt 2499 1 5,
   opAt 2500 .SHR,
   opAt 2501 (.Dup ⟨3, by decide⟩),
   opAt 2502 (.Dup ⟨1, by decide⟩),
   pushAt 2503 1 5,
   opAt 2504 .SHL,
   opAt 2505 .SUB,
   pushAt 2506 1 3,
   opAt 2507 .SHL,
   pushAt 2508 1 96,
   opAt 2509 .CALLDATALOAD,
   opAt 2510 (.Swap ⟨0, by decide⟩),
   opAt 2511 .SHR,
   opAt 2512 (.Dup ⟨2, by decide⟩),
   pushAt 2513 2 992,
   opAt 2514 .ADD,
   opAt 2515 .MSTORE,
   pushAt 2516 1 1,
   pushAt 2517 2 1649,
   opAt 2518 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
