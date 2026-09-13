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
  [opAt 2123 .JUMPDEST,
   opAt 2124 (.Dup ⟨0, by decide⟩),
   opAt 2125 .MLOAD,
   opAt 2126 .NOT,
   opAt 2127 (.Dup ⟨2, by decide⟩),
   opAt 2128 .ADD,
   opAt 2129 (.Dup ⟨0, by decide⟩),
   opAt 2130 (.Swap ⟨2, by decide⟩),
   opAt 2131 .GT,
   opAt 2132 (.Swap ⟨1, by decide⟩),
   opAt 2133 (.Dup ⟨1, by decide⟩),
   pushAt 2134 2 1280,
   opAt 2135 .ADD,
   opAt 2136 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2137 (.Dup ⟨0, by decide⟩),
   pushAt 2138 1 31,
   opAt 2139 .NOT,
   opAt 2140 .ADD,
   opAt 2141 (.Swap ⟨0, by decide⟩),
   pushAt 2142 2 2863,
   opAt 2143 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2339 .JUMPDEST,
   pushAt 2340 2 832,
   opAt 2341 (.Dup ⟨1, by decide⟩),
   opAt 2342 .SUB,
   opAt 2343 .MLOAD,
   opAt 2344 (.Dup ⟨2, by decide⟩),
   opAt 2345 (.Dup ⟨6, by decide⟩),
   opAt 2346 (.Dup ⟨2, by decide⟩),
   opAt 2347 .MUL,
   opAt 2348 (.Swap ⟨1, by decide⟩),
   opAt 2349 (.Dup ⟨7, by decide⟩),
   opAt 2350 .MULMOD,
   opAt 2351 (.Dup ⟨1, by decide⟩),
   opAt 2352 (.Dup ⟨1, by decide⟩),
   opAt 2353 .LT,
   opAt 2354 .SUB,
   opAt 2355 (.Dup ⟨5, by decide⟩),
   opAt 2356 (.Dup ⟨2, by decide⟩),
   opAt 2357 .ADD,
   opAt 2358 (.Dup ⟨0, by decide⟩),
   opAt 2359 (.Swap ⟨6, by decide⟩),
   opAt 2360 .GT,
   opAt 2361 .SUB,
   opAt 2362 .SUB,
   opAt 2363 (.Dup ⟨4, by decide⟩),
   opAt 2364 (.Dup ⟨2, by decide⟩),
   opAt 2365 .MLOAD,
   opAt 2366 .ADD,
   opAt 2367 (.Dup ⟨0, by decide⟩),
   opAt 2368 (.Swap ⟨5, by decide⟩),
   opAt 2369 .GT,
   opAt 2370 .ADD,
   opAt 2371 (.Swap ⟨3, by decide⟩),
   opAt 2372 (.Dup ⟨1, by decide⟩),
   opAt 2373 .MSTORE,
   opAt 2374 (.Dup ⟨2, by decide⟩),
   opAt 2375 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2487 2 2080,
   opAt 2488 (.Dup ⟨1, by decide⟩),
   opAt 2489 .GT,
   pushAt 2490 2 3152,
   opAt 2491 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2531 .JUMPDEST,
   opAt 2532 (.Dup ⟨0, by decide⟩),
   opAt 2533 .MLOAD,
   opAt 2534 (.Dup ⟨1, by decide⟩),
   pushAt 2535 2 2112,
   opAt 2536 (.Swap ⟨0, by decide⟩),
   opAt 2537 .SUB,
   opAt 2538 .MLOAD,
   opAt 2539 (.Dup ⟨1, by decide⟩),
   opAt 2540 .ADD,
   opAt 2541 (.Dup ⟨0, by decide⟩),
   opAt 2542 (.Dup ⟨2, by decide⟩),
   opAt 2543 .GT,
   opAt 2544 (.Swap ⟨1, by decide⟩),
   opAt 2545 .POP,
   opAt 2546 (.Dup ⟨3, by decide⟩),
   opAt 2547 .ADD,
   opAt 2548 (.Dup ⟨0, by decide⟩),
   opAt 2549 (.Dup ⟨4, by decide⟩),
   opAt 2550 .GT,
   opAt 2551 (.Swap ⟨3, by decide⟩),
   opAt 2552 .POP,
   opAt 2553 (.Dup ⟨2, by decide⟩),
   opAt 2554 .MSTORE,
   opAt 2555 (.Swap ⟨0, by decide⟩),
   opAt 2556 (.Swap ⟨1, by decide⟩),
   opAt 2557 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2558 (.Swap ⟨0, by decide⟩),
   pushAt 2559 1 31,
   opAt 2560 .NOT,
   opAt 2561 .ADD,
   pushAt 2562 2 2111,
   opAt 2563 (.Dup ⟨1, by decide⟩),
   opAt 2564 .GT,
   pushAt 2565 2 3372,
   opAt 2566 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2591 .JUMPDEST,
   opAt 2592 (.Dup ⟨0, by decide⟩),
   opAt 2593 .MLOAD,
   pushAt 2594 2 2112,
   opAt 2595 (.Dup ⟨2, by decide⟩),
   opAt 2596 .SUB,
   opAt 2597 .MLOAD,
   opAt 2598 (.Dup ⟨1, by decide⟩),
   opAt 2599 (.Dup ⟨1, by decide⟩),
   opAt 2600 .GT,
   opAt 2601 (.Swap ⟨1, by decide⟩),
   opAt 2602 .SUB,
   opAt 2603 (.Dup ⟨3, by decide⟩),
   opAt 2604 (.Dup ⟨1, by decide⟩),
   opAt 2605 .LT,
   opAt 2606 (.Swap ⟨0, by decide⟩),
   opAt 2607 (.Dup ⟨4, by decide⟩),
   opAt 2608 (.Swap ⟨0, by decide⟩),
   opAt 2609 .SUB,
   opAt 2610 (.Dup ⟨3, by decide⟩),
   opAt 2611 .MSTORE,
   opAt 2612 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2613 (.Swap ⟨1, by decide⟩),
   opAt 2614 .POP,
   pushAt 2615 1 31,
   opAt 2616 .NOT,
   opAt 2617 .ADD,
   pushAt 2618 2 2111,
   opAt 2619 (.Dup ⟨1, by decide⟩),
   opAt 2620 .GT,
   pushAt 2621 2 3451,
   opAt 2622 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
