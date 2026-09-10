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
  [opAt 2454 .JUMPDEST,
   opAt 2455 (.Dup ⟨0, by decide⟩),
   opAt 2456 (.Dup ⟨3, by decide⟩),
   opAt 2457 .EQ,
   pushAt 2458 0 0,
   opAt 2459 .MLOAD,
   pushAt 2460 1 255,
   opAt 2461 .SHR,
   opAt 2462 .AND,
   opAt 2463 .ISZERO,
   pushAt 2464 2 3455,
   opAt 2465 .JUMPI]

/-- pc 3877..3407, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2466 (.Dup ⟨0, by decide⟩),
   pushAt 2467 1 96,
   pushAt 2468 2 1024,
   opAt 2469 .CALLDATACOPY,
   pushAt 2470 2 1691,
   pushAt 2471 2 2048,
   pushAt 2472 2 1024,
   pushAt 2473 2 6144,
   pushAt 2474 2 4493,
   opAt 2475 .JUMP]

/-- pc 3644..3424, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2476 2 1691,
   pushAt 2477 2 2048,
   pushAt 2478 2 6144,
   pushAt 2479 2 1024,
   pushAt 2480 2 4493,
   opAt 2481 .JUMP]

/-- pc 3425..3458, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2482 .JUMPDEST,
   opAt 2483 (.Dup ⟨2, by decide⟩),
   pushAt 2484 1 31,
   opAt 2485 .ADD,
   pushAt 2486 1 5,
   opAt 2487 .SHR,
   opAt 2488 (.Dup ⟨3, by decide⟩),
   opAt 2489 (.Dup ⟨1, by decide⟩),
   pushAt 2490 1 5,
   opAt 2491 .SHL,
   opAt 2492 .SUB,
   pushAt 2493 1 3,
   opAt 2494 .SHL,
   pushAt 2495 1 96,
   opAt 2496 .CALLDATALOAD,
   opAt 2497 (.Swap ⟨0, by decide⟩),
   opAt 2498 .SHR,
   opAt 2499 (.Dup ⟨2, by decide⟩),
   pushAt 2500 2 992,
   opAt 2501 .ADD,
   opAt 2502 .MSTORE,
   pushAt 2503 1 1,
   pushAt 2504 2 1605,
   opAt 2505 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
