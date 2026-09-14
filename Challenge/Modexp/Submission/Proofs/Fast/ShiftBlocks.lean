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
  [opAt 2126 .JUMPDEST,
   opAt 2127 (.Dup ⟨0, by decide⟩),
   opAt 2128 .MLOAD,
   opAt 2129 .NOT,
   opAt 2130 (.Dup ⟨2, by decide⟩),
   opAt 2131 .ADD,
   opAt 2132 (.Dup ⟨0, by decide⟩),
   opAt 2133 (.Swap ⟨2, by decide⟩),
   opAt 2134 .GT,
   opAt 2135 (.Swap ⟨1, by decide⟩),
   opAt 2136 (.Dup ⟨1, by decide⟩),
   pushAt 2137 2 1280,
   opAt 2138 .ADD,
   opAt 2139 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2140 (.Dup ⟨0, by decide⟩),
   pushAt 2141 1 31,
   opAt 2142 .NOT,
   opAt 2143 .ADD,
   opAt 2144 (.Swap ⟨0, by decide⟩),
   pushAt 2145 2 2863,
   opAt 2146 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2340 .JUMPDEST,
   pushAt 2341 2 832,
   opAt 2342 (.Dup ⟨1, by decide⟩),
   opAt 2343 .SUB,
   opAt 2344 .MLOAD,
   opAt 2345 (.Dup ⟨2, by decide⟩),
   opAt 2346 (.Dup ⟨6, by decide⟩),
   opAt 2347 (.Dup ⟨2, by decide⟩),
   opAt 2348 .MUL,
   opAt 2349 (.Swap ⟨1, by decide⟩),
   opAt 2350 (.Dup ⟨7, by decide⟩),
   opAt 2351 .MULMOD,
   opAt 2352 (.Dup ⟨1, by decide⟩),
   opAt 2353 (.Dup ⟨1, by decide⟩),
   opAt 2354 .LT,
   opAt 2355 .SUB,
   opAt 2356 (.Dup ⟨5, by decide⟩),
   opAt 2357 (.Dup ⟨2, by decide⟩),
   opAt 2358 .ADD,
   opAt 2359 (.Dup ⟨0, by decide⟩),
   opAt 2360 (.Swap ⟨6, by decide⟩),
   opAt 2361 .GT,
   opAt 2362 .SUB,
   opAt 2363 .SUB,
   opAt 2364 (.Dup ⟨4, by decide⟩),
   opAt 2365 (.Dup ⟨2, by decide⟩),
   opAt 2366 .MLOAD,
   opAt 2367 .ADD,
   opAt 2368 (.Dup ⟨0, by decide⟩),
   opAt 2369 (.Swap ⟨5, by decide⟩),
   opAt 2370 .GT,
   opAt 2371 .ADD,
   opAt 2372 (.Swap ⟨3, by decide⟩),
   opAt 2373 (.Dup ⟨1, by decide⟩),
   opAt 2374 .MSTORE,
   opAt 2375 (.Dup ⟨2, by decide⟩),
   opAt 2376 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2488 2 2080,
   opAt 2489 (.Dup ⟨1, by decide⟩),
   opAt 2490 .GT,
   pushAt 2491 2 3150,
   opAt 2492 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2532 .JUMPDEST,
   opAt 2533 (.Dup ⟨0, by decide⟩),
   opAt 2534 .MLOAD,
   opAt 2535 (.Dup ⟨1, by decide⟩),
   pushAt 2536 2 2112,
   opAt 2537 (.Swap ⟨0, by decide⟩),
   opAt 2538 .SUB,
   opAt 2539 .MLOAD,
   opAt 2540 (.Dup ⟨1, by decide⟩),
   opAt 2541 .ADD,
   opAt 2542 (.Dup ⟨0, by decide⟩),
   opAt 2543 (.Dup ⟨2, by decide⟩),
   opAt 2544 .GT,
   opAt 2545 (.Swap ⟨1, by decide⟩),
   opAt 2546 .POP,
   opAt 2547 (.Dup ⟨3, by decide⟩),
   opAt 2548 .ADD,
   opAt 2549 (.Dup ⟨0, by decide⟩),
   opAt 2550 (.Dup ⟨4, by decide⟩),
   opAt 2551 .GT,
   opAt 2552 (.Swap ⟨3, by decide⟩),
   opAt 2553 .POP,
   opAt 2554 (.Dup ⟨2, by decide⟩),
   opAt 2555 .MSTORE,
   opAt 2556 (.Swap ⟨0, by decide⟩),
   opAt 2557 (.Swap ⟨1, by decide⟩),
   opAt 2558 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2559 (.Swap ⟨0, by decide⟩),
   pushAt 2560 1 31,
   opAt 2561 .NOT,
   opAt 2562 .ADD,
   pushAt 2563 2 2111,
   opAt 2564 (.Dup ⟨1, by decide⟩),
   opAt 2565 .GT,
   pushAt 2566 2 3370,
   opAt 2567 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2592 .JUMPDEST,
   opAt 2593 (.Dup ⟨0, by decide⟩),
   opAt 2594 .MLOAD,
   pushAt 2595 2 2112,
   opAt 2596 (.Dup ⟨2, by decide⟩),
   opAt 2597 .SUB,
   opAt 2598 .MLOAD,
   opAt 2599 (.Dup ⟨1, by decide⟩),
   opAt 2600 (.Dup ⟨1, by decide⟩),
   opAt 2601 .GT,
   opAt 2602 (.Swap ⟨1, by decide⟩),
   opAt 2603 .SUB,
   opAt 2604 (.Dup ⟨3, by decide⟩),
   opAt 2605 (.Dup ⟨1, by decide⟩),
   opAt 2606 .LT,
   opAt 2607 (.Swap ⟨0, by decide⟩),
   opAt 2608 (.Dup ⟨4, by decide⟩),
   opAt 2609 (.Swap ⟨0, by decide⟩),
   opAt 2610 .SUB,
   opAt 2611 (.Dup ⟨3, by decide⟩),
   opAt 2612 .MSTORE,
   opAt 2613 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2614 (.Swap ⟨1, by decide⟩),
   opAt 2615 .POP,
   pushAt 2616 1 31,
   opAt 2617 .NOT,
   opAt 2618 .ADD,
   pushAt 2619 2 2111,
   opAt 2620 (.Dup ⟨1, by decide⟩),
   opAt 2621 .GT,
   pushAt 2622 2 3449,
   opAt 2623 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
