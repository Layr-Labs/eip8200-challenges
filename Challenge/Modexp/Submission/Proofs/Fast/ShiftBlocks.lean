import Challenge.Modexp.Submission.Proofs.Fast.ShiftPaths
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Loop-body blocks of the shift-reduce routine split before their exit tests, so
that each block reduction stays small enough for the kernel. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The negation loop body up to its exit test (`blk2896` instructions 0..14). -/
def blk2896a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2130 .JUMPDEST,
   opAt 2131 (.Dup ⟨0, by decide⟩),
   opAt 2132 .MLOAD,
   opAt 2133 .NOT,
   opAt 2134 (.Dup ⟨2, by decide⟩),
   opAt 2135 .ADD,
   opAt 2136 (.Dup ⟨0, by decide⟩),
   opAt 2137 (.Swap ⟨2, by decide⟩),
   opAt 2138 .GT,
   opAt 2139 (.Swap ⟨1, by decide⟩),
   opAt 2140 (.Dup ⟨1, by decide⟩),
   pushAt 2141 2 1280,
   opAt 2142 .ADD,
   opAt 2143 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2144 (.Dup ⟨0, by decide⟩),
   pushAt 2145 1 31,
   opAt 2146 .NOT,
   opAt 2147 .ADD,
   opAt 2148 (.Swap ⟨0, by decide⟩),
   pushAt 2149 2 2868,
   opAt 2150 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2347 .JUMPDEST,
   pushAt 2348 2 832,
   opAt 2349 (.Dup ⟨1, by decide⟩),
   opAt 2350 .SUB,
   opAt 2351 .MLOAD,
   opAt 2352 (.Dup ⟨2, by decide⟩),
   opAt 2353 (.Dup ⟨6, by decide⟩),
   opAt 2354 (.Dup ⟨2, by decide⟩),
   opAt 2355 .MUL,
   opAt 2356 (.Swap ⟨1, by decide⟩),
   opAt 2357 (.Dup ⟨7, by decide⟩),
   opAt 2358 .MULMOD,
   opAt 2359 (.Dup ⟨1, by decide⟩),
   opAt 2360 (.Dup ⟨1, by decide⟩),
   opAt 2361 .LT,
   opAt 2362 .SUB,
   opAt 2363 (.Dup ⟨5, by decide⟩),
   opAt 2364 (.Dup ⟨2, by decide⟩),
   opAt 2365 .ADD,
   opAt 2366 (.Dup ⟨0, by decide⟩),
   opAt 2367 (.Swap ⟨6, by decide⟩),
   opAt 2368 .GT,
   opAt 2369 .SUB,
   opAt 2370 .SUB,
   opAt 2371 (.Dup ⟨4, by decide⟩),
   opAt 2372 (.Dup ⟨2, by decide⟩),
   opAt 2373 .MLOAD,
   opAt 2374 .ADD,
   opAt 2375 (.Dup ⟨0, by decide⟩),
   opAt 2376 (.Swap ⟨5, by decide⟩),
   opAt 2377 .GT,
   opAt 2378 .ADD,
   opAt 2379 (.Swap ⟨3, by decide⟩),
   opAt 2380 (.Dup ⟨1, by decide⟩),
   opAt 2381 .MSTORE,
   opAt 2382 (.Dup ⟨2, by decide⟩),
   opAt 2383 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2495 2 2080,
   opAt 2496 (.Dup ⟨1, by decide⟩),
   opAt 2497 .GT,
   pushAt 2498 2 3158,
   opAt 2499 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2539 .JUMPDEST,
   opAt 2540 (.Dup ⟨0, by decide⟩),
   opAt 2541 .MLOAD,
   opAt 2542 (.Dup ⟨1, by decide⟩),
   pushAt 2543 2 2112,
   opAt 2544 (.Swap ⟨0, by decide⟩),
   opAt 2545 .SUB,
   opAt 2546 .MLOAD,
   opAt 2547 (.Dup ⟨1, by decide⟩),
   opAt 2548 .ADD,
   opAt 2549 (.Dup ⟨0, by decide⟩),
   opAt 2550 (.Dup ⟨2, by decide⟩),
   opAt 2551 .GT,
   opAt 2552 (.Swap ⟨1, by decide⟩),
   opAt 2553 .POP,
   opAt 2554 (.Dup ⟨3, by decide⟩),
   opAt 2555 .ADD,
   opAt 2556 (.Dup ⟨0, by decide⟩),
   opAt 2557 (.Dup ⟨4, by decide⟩),
   opAt 2558 .GT,
   opAt 2559 (.Swap ⟨3, by decide⟩),
   opAt 2560 .POP,
   opAt 2561 (.Dup ⟨2, by decide⟩),
   opAt 2562 .MSTORE,
   opAt 2563 (.Swap ⟨0, by decide⟩),
   opAt 2564 (.Swap ⟨1, by decide⟩),
   opAt 2565 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2566 (.Swap ⟨0, by decide⟩),
   pushAt 2567 1 31,
   opAt 2568 .NOT,
   opAt 2569 .ADD,
   pushAt 2570 2 2111,
   opAt 2571 (.Dup ⟨1, by decide⟩),
   opAt 2572 .GT,
   pushAt 2573 2 3378,
   opAt 2574 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2599 .JUMPDEST,
   opAt 2600 (.Dup ⟨0, by decide⟩),
   opAt 2601 .MLOAD,
   pushAt 2602 2 2112,
   opAt 2603 (.Dup ⟨2, by decide⟩),
   opAt 2604 .SUB,
   opAt 2605 .MLOAD,
   opAt 2606 (.Dup ⟨1, by decide⟩),
   opAt 2607 (.Dup ⟨1, by decide⟩),
   opAt 2608 .GT,
   opAt 2609 (.Swap ⟨1, by decide⟩),
   opAt 2610 .SUB,
   opAt 2611 (.Dup ⟨3, by decide⟩),
   opAt 2612 (.Dup ⟨1, by decide⟩),
   opAt 2613 .LT,
   opAt 2614 (.Swap ⟨0, by decide⟩),
   opAt 2615 (.Dup ⟨4, by decide⟩),
   opAt 2616 (.Swap ⟨0, by decide⟩),
   opAt 2617 .SUB,
   opAt 2618 (.Dup ⟨3, by decide⟩),
   opAt 2619 .MSTORE,
   opAt 2620 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2621 (.Swap ⟨1, by decide⟩),
   opAt 2622 .POP,
   pushAt 2623 1 31,
   opAt 2624 .NOT,
   opAt 2625 .ADD,
   pushAt 2626 2 2111,
   opAt 2627 (.Dup ⟨1, by decide⟩),
   opAt 2628 .GT,
   pushAt 2629 2 3457,
   opAt 2630 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
