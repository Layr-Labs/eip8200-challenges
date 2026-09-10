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
  [opAt 2420 .JUMPDEST,
   opAt 2421 (.Dup ⟨0, by decide⟩),
   opAt 2422 (.Dup ⟨3, by decide⟩),
   opAt 2423 .EQ,
   pushAt 2424 0 0,
   opAt 2425 .MLOAD,
   pushAt 2426 1 255,
   opAt 2427 .SHR,
   opAt 2428 .AND,
   opAt 2429 .ISZERO,
   pushAt 2430 2 3387,
   opAt 2431 .JUMPI]

/-- pc 3877..3407, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2432 (.Dup ⟨0, by decide⟩),
   pushAt 2433 1 96,
   pushAt 2434 2 1024,
   opAt 2435 .CALLDATACOPY,
   pushAt 2436 2 1737,
   pushAt 2437 2 2048,
   pushAt 2438 2 1024,
   pushAt 2439 2 6144,
   pushAt 2440 2 4428,
   opAt 2441 .JUMP]

/-- pc 3644..3424, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2442 2 1737,
   pushAt 2443 2 2048,
   pushAt 2444 2 6144,
   pushAt 2445 2 1024,
   pushAt 2446 2 4428,
   opAt 2447 .JUMP]

/-- pc 3425..3458, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2448 .JUMPDEST,
   opAt 2449 (.Dup ⟨2, by decide⟩),
   pushAt 2450 1 31,
   opAt 2451 .ADD,
   pushAt 2452 1 5,
   opAt 2453 .SHR,
   opAt 2454 (.Dup ⟨3, by decide⟩),
   opAt 2455 (.Dup ⟨1, by decide⟩),
   pushAt 2456 1 5,
   opAt 2457 .SHL,
   opAt 2458 .SUB,
   pushAt 2459 1 3,
   opAt 2460 .SHL,
   pushAt 2461 1 96,
   opAt 2462 .CALLDATALOAD,
   opAt 2463 (.Swap ⟨0, by decide⟩),
   opAt 2464 .SHR,
   opAt 2465 (.Dup ⟨2, by decide⟩),
   pushAt 2466 2 992,
   opAt 2467 .ADD,
   opAt 2468 .MSTORE,
   pushAt 2469 1 1,
   pushAt 2470 2 1651,
   opAt 2471 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
