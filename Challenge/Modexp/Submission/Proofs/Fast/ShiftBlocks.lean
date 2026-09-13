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
  [opAt 2345 .JUMPDEST,
   pushAt 2346 2 832,
   opAt 2347 (.Dup ⟨1, by decide⟩),
   opAt 2348 .SUB,
   opAt 2349 .MLOAD,
   opAt 2350 (.Dup ⟨2, by decide⟩),
   opAt 2351 (.Dup ⟨6, by decide⟩),
   opAt 2352 (.Dup ⟨2, by decide⟩),
   opAt 2353 .MUL,
   opAt 2354 (.Swap ⟨1, by decide⟩),
   opAt 2355 (.Dup ⟨7, by decide⟩),
   opAt 2356 .MULMOD,
   opAt 2357 (.Dup ⟨1, by decide⟩),
   opAt 2358 (.Dup ⟨1, by decide⟩),
   opAt 2359 .LT,
   opAt 2360 .SUB,
   opAt 2361 (.Dup ⟨5, by decide⟩),
   opAt 2362 (.Dup ⟨2, by decide⟩),
   opAt 2363 .ADD,
   opAt 2364 (.Dup ⟨0, by decide⟩),
   opAt 2365 (.Swap ⟨6, by decide⟩),
   opAt 2366 .GT,
   opAt 2367 .SUB,
   opAt 2368 .SUB,
   opAt 2369 (.Dup ⟨4, by decide⟩),
   opAt 2370 (.Dup ⟨2, by decide⟩),
   opAt 2371 .MLOAD,
   opAt 2372 .ADD,
   opAt 2373 (.Dup ⟨0, by decide⟩),
   opAt 2374 (.Swap ⟨5, by decide⟩),
   opAt 2375 .GT,
   opAt 2376 .ADD,
   opAt 2377 (.Swap ⟨3, by decide⟩),
   opAt 2378 (.Dup ⟨1, by decide⟩),
   opAt 2379 .MSTORE,
   opAt 2380 (.Dup ⟨2, by decide⟩),
   opAt 2381 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2493 2 2080,
   opAt 2494 (.Dup ⟨1, by decide⟩),
   opAt 2495 .GT,
   pushAt 2496 2 3156,
   opAt 2497 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2537 .JUMPDEST,
   opAt 2538 (.Dup ⟨0, by decide⟩),
   opAt 2539 .MLOAD,
   opAt 2540 (.Dup ⟨1, by decide⟩),
   pushAt 2541 2 2112,
   opAt 2542 (.Swap ⟨0, by decide⟩),
   opAt 2543 .SUB,
   opAt 2544 .MLOAD,
   opAt 2545 (.Dup ⟨1, by decide⟩),
   opAt 2546 .ADD,
   opAt 2547 (.Dup ⟨0, by decide⟩),
   opAt 2548 (.Dup ⟨2, by decide⟩),
   opAt 2549 .GT,
   opAt 2550 (.Swap ⟨1, by decide⟩),
   opAt 2551 .POP,
   opAt 2552 (.Dup ⟨3, by decide⟩),
   opAt 2553 .ADD,
   opAt 2554 (.Dup ⟨0, by decide⟩),
   opAt 2555 (.Dup ⟨4, by decide⟩),
   opAt 2556 .GT,
   opAt 2557 (.Swap ⟨3, by decide⟩),
   opAt 2558 .POP,
   opAt 2559 (.Dup ⟨2, by decide⟩),
   opAt 2560 .MSTORE,
   opAt 2561 (.Swap ⟨0, by decide⟩),
   opAt 2562 (.Swap ⟨1, by decide⟩),
   opAt 2563 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2564 (.Swap ⟨0, by decide⟩),
   pushAt 2565 1 31,
   opAt 2566 .NOT,
   opAt 2567 .ADD,
   pushAt 2568 2 2111,
   opAt 2569 (.Dup ⟨1, by decide⟩),
   opAt 2570 .GT,
   pushAt 2571 2 3376,
   opAt 2572 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2597 .JUMPDEST,
   opAt 2598 (.Dup ⟨0, by decide⟩),
   opAt 2599 .MLOAD,
   pushAt 2600 2 2112,
   opAt 2601 (.Dup ⟨2, by decide⟩),
   opAt 2602 .SUB,
   opAt 2603 .MLOAD,
   opAt 2604 (.Dup ⟨1, by decide⟩),
   opAt 2605 (.Dup ⟨1, by decide⟩),
   opAt 2606 .GT,
   opAt 2607 (.Swap ⟨1, by decide⟩),
   opAt 2608 .SUB,
   opAt 2609 (.Dup ⟨3, by decide⟩),
   opAt 2610 (.Dup ⟨1, by decide⟩),
   opAt 2611 .LT,
   opAt 2612 (.Swap ⟨0, by decide⟩),
   opAt 2613 (.Dup ⟨4, by decide⟩),
   opAt 2614 (.Swap ⟨0, by decide⟩),
   opAt 2615 .SUB,
   opAt 2616 (.Dup ⟨3, by decide⟩),
   opAt 2617 .MSTORE,
   opAt 2618 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2619 (.Swap ⟨1, by decide⟩),
   opAt 2620 .POP,
   pushAt 2621 1 31,
   opAt 2622 .NOT,
   opAt 2623 .ADD,
   pushAt 2624 2 2111,
   opAt 2625 (.Dup ⟨1, by decide⟩),
   opAt 2626 .GT,
   pushAt 2627 2 3455,
   opAt 2628 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
