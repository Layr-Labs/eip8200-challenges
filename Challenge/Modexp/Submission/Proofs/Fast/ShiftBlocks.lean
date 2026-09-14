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
  [opAt 2128 .JUMPDEST,
   opAt 2129 (.Dup ⟨0, by decide⟩),
   opAt 2130 .MLOAD,
   opAt 2131 .NOT,
   opAt 2132 (.Dup ⟨2, by decide⟩),
   opAt 2133 .ADD,
   opAt 2134 (.Dup ⟨0, by decide⟩),
   opAt 2135 (.Swap ⟨2, by decide⟩),
   opAt 2136 .GT,
   opAt 2137 (.Swap ⟨1, by decide⟩),
   opAt 2138 (.Dup ⟨1, by decide⟩),
   pushAt 2139 2 1280,
   opAt 2140 .ADD,
   opAt 2141 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2142 (.Dup ⟨0, by decide⟩),
   pushAt 2143 1 31,
   opAt 2144 .NOT,
   opAt 2145 .ADD,
   opAt 2146 (.Swap ⟨0, by decide⟩),
   pushAt 2147 2 2863,
   opAt 2148 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2342 .JUMPDEST,
   pushAt 2343 2 832,
   opAt 2344 (.Dup ⟨1, by decide⟩),
   opAt 2345 .SUB,
   opAt 2346 .MLOAD,
   opAt 2347 (.Dup ⟨2, by decide⟩),
   opAt 2348 (.Dup ⟨6, by decide⟩),
   opAt 2349 (.Dup ⟨2, by decide⟩),
   opAt 2350 .MUL,
   opAt 2351 (.Swap ⟨1, by decide⟩),
   opAt 2352 (.Dup ⟨7, by decide⟩),
   opAt 2353 .MULMOD,
   opAt 2354 (.Dup ⟨1, by decide⟩),
   opAt 2355 (.Dup ⟨1, by decide⟩),
   opAt 2356 .LT,
   opAt 2357 .SUB,
   opAt 2358 (.Dup ⟨5, by decide⟩),
   opAt 2359 (.Dup ⟨2, by decide⟩),
   opAt 2360 .ADD,
   opAt 2361 (.Dup ⟨0, by decide⟩),
   opAt 2362 (.Swap ⟨6, by decide⟩),
   opAt 2363 .GT,
   opAt 2364 .SUB,
   opAt 2365 .SUB,
   opAt 2366 (.Dup ⟨4, by decide⟩),
   opAt 2367 (.Dup ⟨2, by decide⟩),
   opAt 2368 .MLOAD,
   opAt 2369 .ADD,
   opAt 2370 (.Dup ⟨0, by decide⟩),
   opAt 2371 (.Swap ⟨5, by decide⟩),
   opAt 2372 .GT,
   opAt 2373 .ADD,
   opAt 2374 (.Swap ⟨3, by decide⟩),
   opAt 2375 (.Dup ⟨1, by decide⟩),
   opAt 2376 .MSTORE,
   opAt 2377 (.Dup ⟨2, by decide⟩),
   opAt 2378 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2490 2 2080,
   opAt 2491 (.Dup ⟨1, by decide⟩),
   opAt 2492 .GT,
   pushAt 2493 2 3150,
   opAt 2494 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2534 .JUMPDEST,
   opAt 2535 (.Dup ⟨0, by decide⟩),
   opAt 2536 .MLOAD,
   pushAt 2537 2 2112,
   opAt 2538 (.Dup ⟨2, by decide⟩),
   opAt 2539 .JUMPDEST,
   opAt 2540 .SUB,
   opAt 2541 .MLOAD,
   opAt 2542 (.Dup ⟨1, by decide⟩),
   opAt 2543 .ADD,
   opAt 2544 (.Dup ⟨0, by decide⟩),
   opAt 2545 (.Dup ⟨2, by decide⟩),
   opAt 2546 .GT,
   opAt 2547 (.Swap ⟨1, by decide⟩),
   opAt 2548 .POP,
   opAt 2549 (.Dup ⟨3, by decide⟩),
   opAt 2550 .ADD,
   opAt 2551 (.Dup ⟨0, by decide⟩),
   opAt 2552 (.Dup ⟨4, by decide⟩),
   opAt 2553 .GT,
   opAt 2554 (.Swap ⟨3, by decide⟩),
   opAt 2555 .POP,
   opAt 2556 (.Dup ⟨2, by decide⟩),
   opAt 2557 .MSTORE,
   opAt 2558 (.Swap ⟨0, by decide⟩),
   opAt 2559 (.Swap ⟨1, by decide⟩),
   opAt 2560 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2561 (.Swap ⟨0, by decide⟩),
   pushAt 2562 1 31,
   opAt 2563 .NOT,
   opAt 2564 .ADD,
   pushAt 2565 2 2111,
   opAt 2566 (.Dup ⟨1, by decide⟩),
   opAt 2567 .GT,
   pushAt 2568 2 3370,
   opAt 2569 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2594 .JUMPDEST,
   opAt 2595 (.Dup ⟨0, by decide⟩),
   opAt 2596 .MLOAD,
   pushAt 2597 2 2112,
   opAt 2598 (.Dup ⟨2, by decide⟩),
   opAt 2599 .SUB,
   opAt 2600 .MLOAD,
   opAt 2601 (.Dup ⟨1, by decide⟩),
   opAt 2602 (.Dup ⟨1, by decide⟩),
   opAt 2603 .GT,
   opAt 2604 (.Swap ⟨1, by decide⟩),
   opAt 2605 .SUB,
   opAt 2606 (.Dup ⟨3, by decide⟩),
   opAt 2607 (.Dup ⟨1, by decide⟩),
   opAt 2608 .LT,
   opAt 2609 (.Swap ⟨0, by decide⟩),
   opAt 2610 (.Dup ⟨4, by decide⟩),
   opAt 2611 (.Swap ⟨0, by decide⟩),
   opAt 2612 .SUB,
   opAt 2613 (.Dup ⟨3, by decide⟩),
   opAt 2614 .MSTORE,
   opAt 2615 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2616 (.Swap ⟨1, by decide⟩),
   opAt 2617 .POP,
   pushAt 2618 1 31,
   opAt 2619 .NOT,
   opAt 2620 .ADD,
   pushAt 2621 2 2111,
   opAt 2622 (.Dup ⟨1, by decide⟩),
   opAt 2623 .GT,
   pushAt 2624 2 3449,
   opAt 2625 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
