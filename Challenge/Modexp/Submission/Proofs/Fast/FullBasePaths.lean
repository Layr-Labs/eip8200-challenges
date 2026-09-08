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

/-- pc 3606..3620, indices 2361..2372: size/top-bit guard. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2495 .JUMPDEST,
   opAt 2496 (.Dup ⟨0, by decide⟩),
   opAt 2497 (.Dup ⟨3, by decide⟩),
   opAt 2498 .EQ,
   pushAt 2499 0 0,
   opAt 2500 .MLOAD,
   pushAt 2501 1 255,
   opAt 2502 .SHR,
   opAt 2503 .AND,
   opAt 2504 .ISZERO,
   pushAt 2505 2 3674,
   opAt 2506 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2507 (.Dup ⟨0, by decide⟩),
   pushAt 2508 1 96,
   pushAt 2509 2 1024,
   opAt 2510 .CALLDATACOPY,
   pushAt 2511 2 1755,
   pushAt 2512 2 2048,
   pushAt 2513 2 1024,
   pushAt 2514 2 6144,
   pushAt 2515 2 1939,
   opAt 2516 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2517 .JUMPDEST,
   pushAt 2518 2 1755,
   pushAt 2519 2 2048,
   pushAt 2520 2 6144,
   pushAt 2521 2 1024,
   pushAt 2522 2 1939,
   opAt 2523 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2524 .JUMPDEST,
   opAt 2525 (.Dup ⟨2, by decide⟩),
   pushAt 2526 1 31,
   opAt 2527 .ADD,
   pushAt 2528 1 5,
   opAt 2529 .SHR,
   opAt 2530 (.Dup ⟨3, by decide⟩),
   opAt 2531 (.Dup ⟨1, by decide⟩),
   pushAt 2532 1 5,
   opAt 2533 .SHL,
   opAt 2534 .SUB,
   pushAt 2535 1 3,
   opAt 2536 .SHL,
   pushAt 2537 1 96,
   opAt 2538 .CALLDATALOAD,
   opAt 2539 (.Swap ⟨0, by decide⟩),
   opAt 2540 .SHR,
   opAt 2541 (.Dup ⟨2, by decide⟩),
   pushAt 2542 2 992,
   opAt 2543 .ADD,
   opAt 2544 .MSTORE,
   pushAt 2545 1 1,
   pushAt 2546 2 1668,
   opAt 2547 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
