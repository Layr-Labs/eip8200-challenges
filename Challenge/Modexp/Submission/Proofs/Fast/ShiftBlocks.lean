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
  [opAt 2127 .JUMPDEST,
   opAt 2128 (.Dup ⟨0, by decide⟩),
   opAt 2129 .MLOAD,
   opAt 2130 .NOT,
   opAt 2131 (.Dup ⟨2, by decide⟩),
   opAt 2132 .ADD,
   opAt 2133 (.Dup ⟨0, by decide⟩),
   opAt 2134 (.Swap ⟨2, by decide⟩),
   opAt 2135 .GT,
   opAt 2136 (.Swap ⟨1, by decide⟩),
   opAt 2137 (.Dup ⟨1, by decide⟩),
   pushAt 2138 2 1280,
   opAt 2139 .ADD,
   opAt 2140 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2141 (.Dup ⟨0, by decide⟩),
   pushAt 2142 1 31,
   opAt 2143 .NOT,
   opAt 2144 .ADD,
   opAt 2145 (.Swap ⟨0, by decide⟩),
   pushAt 2146 2 2863,
   opAt 2147 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2343 .JUMPDEST,
   pushAt 2344 2 832,
   opAt 2345 (.Dup ⟨1, by decide⟩),
   opAt 2346 .SUB,
   opAt 2347 .MLOAD,
   opAt 2348 (.Dup ⟨2, by decide⟩),
   opAt 2349 (.Dup ⟨6, by decide⟩),
   opAt 2350 (.Dup ⟨2, by decide⟩),
   opAt 2351 .MUL,
   opAt 2352 (.Swap ⟨1, by decide⟩),
   opAt 2353 (.Dup ⟨7, by decide⟩),
   opAt 2354 .MULMOD,
   opAt 2355 (.Dup ⟨1, by decide⟩),
   opAt 2356 (.Dup ⟨1, by decide⟩),
   opAt 2357 .LT,
   opAt 2358 .SUB,
   opAt 2359 (.Dup ⟨5, by decide⟩),
   opAt 2360 (.Dup ⟨2, by decide⟩),
   opAt 2361 .ADD,
   opAt 2362 (.Dup ⟨0, by decide⟩),
   opAt 2363 (.Swap ⟨6, by decide⟩),
   opAt 2364 .GT,
   opAt 2365 .SUB,
   opAt 2366 .SUB,
   opAt 2367 (.Dup ⟨4, by decide⟩),
   opAt 2368 (.Dup ⟨2, by decide⟩),
   opAt 2369 .MLOAD,
   opAt 2370 .ADD,
   opAt 2371 (.Dup ⟨0, by decide⟩),
   opAt 2372 (.Swap ⟨5, by decide⟩),
   opAt 2373 .GT,
   opAt 2374 .ADD,
   opAt 2375 (.Swap ⟨3, by decide⟩),
   opAt 2376 (.Dup ⟨1, by decide⟩),
   opAt 2377 .MSTORE,
   opAt 2378 (.Dup ⟨2, by decide⟩),
   opAt 2379 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2491 2 2080,
   opAt 2492 (.Dup ⟨1, by decide⟩),
   opAt 2493 .GT,
   pushAt 2494 2 3152,
   opAt 2495 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2535 .JUMPDEST,
   opAt 2536 (.Dup ⟨0, by decide⟩),
   opAt 2537 .MLOAD,
   opAt 2538 (.Dup ⟨1, by decide⟩),
   pushAt 2539 2 2112,
   opAt 2540 (.Swap ⟨0, by decide⟩),
   opAt 2541 .SUB,
   opAt 2542 .MLOAD,
   opAt 2543 (.Dup ⟨1, by decide⟩),
   opAt 2544 .ADD,
   opAt 2545 (.Dup ⟨0, by decide⟩),
   opAt 2546 (.Dup ⟨2, by decide⟩),
   opAt 2547 .GT,
   opAt 2548 (.Swap ⟨1, by decide⟩),
   opAt 2549 .POP,
   opAt 2550 (.Dup ⟨3, by decide⟩),
   opAt 2551 .ADD,
   opAt 2552 (.Dup ⟨0, by decide⟩),
   opAt 2553 (.Dup ⟨4, by decide⟩),
   opAt 2554 .GT,
   opAt 2555 (.Swap ⟨3, by decide⟩),
   opAt 2556 .POP,
   opAt 2557 (.Dup ⟨2, by decide⟩),
   opAt 2558 .MSTORE,
   opAt 2559 (.Swap ⟨0, by decide⟩),
   opAt 2560 (.Swap ⟨1, by decide⟩),
   opAt 2561 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2562 (.Swap ⟨0, by decide⟩),
   pushAt 2563 1 31,
   opAt 2564 .NOT,
   opAt 2565 .ADD,
   pushAt 2566 2 2111,
   opAt 2567 (.Dup ⟨1, by decide⟩),
   opAt 2568 .GT,
   pushAt 2569 2 3372,
   opAt 2570 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2595 .JUMPDEST,
   opAt 2596 (.Dup ⟨0, by decide⟩),
   opAt 2597 .MLOAD,
   pushAt 2598 2 2112,
   opAt 2599 (.Dup ⟨2, by decide⟩),
   opAt 2600 .SUB,
   opAt 2601 .MLOAD,
   opAt 2602 (.Dup ⟨1, by decide⟩),
   opAt 2603 (.Dup ⟨1, by decide⟩),
   opAt 2604 .GT,
   opAt 2605 (.Swap ⟨1, by decide⟩),
   opAt 2606 .SUB,
   opAt 2607 (.Dup ⟨3, by decide⟩),
   opAt 2608 (.Dup ⟨1, by decide⟩),
   opAt 2609 .LT,
   opAt 2610 (.Swap ⟨0, by decide⟩),
   opAt 2611 (.Dup ⟨4, by decide⟩),
   opAt 2612 (.Swap ⟨0, by decide⟩),
   opAt 2613 .SUB,
   opAt 2614 (.Dup ⟨3, by decide⟩),
   opAt 2615 .MSTORE,
   opAt 2616 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2617 (.Swap ⟨1, by decide⟩),
   opAt 2618 .POP,
   pushAt 2619 1 31,
   opAt 2620 .NOT,
   opAt 2621 .ADD,
   pushAt 2622 2 2111,
   opAt 2623 (.Dup ⟨1, by decide⟩),
   opAt 2624 .GT,
   pushAt 2625 2 3451,
   opAt 2626 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
