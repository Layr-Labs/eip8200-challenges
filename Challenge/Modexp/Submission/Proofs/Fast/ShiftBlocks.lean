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
   pushAt 2145 2 2862,
   opAt 2146 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2338 .JUMPDEST,
   pushAt 2339 2 832,
   opAt 2340 (.Dup ⟨1, by decide⟩),
   opAt 2341 .SUB,
   opAt 2342 .MLOAD,
   opAt 2343 (.Dup ⟨2, by decide⟩),
   opAt 2344 (.Dup ⟨6, by decide⟩),
   opAt 2345 (.Dup ⟨2, by decide⟩),
   opAt 2346 .MUL,
   opAt 2347 (.Swap ⟨1, by decide⟩),
   opAt 2348 (.Dup ⟨7, by decide⟩),
   opAt 2349 .MULMOD,
   opAt 2350 (.Dup ⟨1, by decide⟩),
   opAt 2351 (.Dup ⟨1, by decide⟩),
   opAt 2352 .LT,
   opAt 2353 .SUB,
   opAt 2354 (.Dup ⟨5, by decide⟩),
   opAt 2355 (.Dup ⟨2, by decide⟩),
   opAt 2356 .ADD,
   opAt 2357 (.Dup ⟨0, by decide⟩),
   opAt 2358 (.Swap ⟨6, by decide⟩),
   opAt 2359 .GT,
   opAt 2360 .SUB,
   opAt 2361 .SUB,
   opAt 2362 (.Dup ⟨4, by decide⟩),
   opAt 2363 (.Dup ⟨2, by decide⟩),
   opAt 2364 .MLOAD,
   opAt 2365 .ADD,
   opAt 2366 (.Dup ⟨0, by decide⟩),
   opAt 2367 (.Swap ⟨5, by decide⟩),
   opAt 2368 .GT,
   opAt 2369 .ADD,
   opAt 2370 (.Swap ⟨3, by decide⟩),
   opAt 2371 (.Dup ⟨1, by decide⟩),
   opAt 2372 .MSTORE,
   opAt 2373 (.Dup ⟨2, by decide⟩),
   opAt 2374 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2486 2 2080,
   opAt 2487 (.Dup ⟨1, by decide⟩),
   opAt 2488 .GT,
   pushAt 2489 2 3147,
   opAt 2490 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2530 .JUMPDEST,
   opAt 2531 (.Dup ⟨0, by decide⟩),
   opAt 2532 .MLOAD,
   opAt 2533 (.Dup ⟨1, by decide⟩),
   pushAt 2534 2 2112,
   opAt 2535 (.Swap ⟨0, by decide⟩),
   opAt 2536 .SUB,
   opAt 2537 .MLOAD,
   opAt 2538 (.Dup ⟨1, by decide⟩),
   opAt 2539 .ADD,
   opAt 2540 (.Dup ⟨0, by decide⟩),
   opAt 2541 (.Dup ⟨2, by decide⟩),
   opAt 2542 .GT,
   opAt 2543 (.Swap ⟨1, by decide⟩),
   opAt 2544 .POP,
   opAt 2545 (.Dup ⟨3, by decide⟩),
   opAt 2546 .ADD,
   opAt 2547 (.Dup ⟨0, by decide⟩),
   opAt 2548 (.Dup ⟨4, by decide⟩),
   opAt 2549 .GT,
   opAt 2550 (.Swap ⟨3, by decide⟩),
   opAt 2551 .POP,
   opAt 2552 (.Dup ⟨2, by decide⟩),
   opAt 2553 .MSTORE,
   opAt 2554 (.Swap ⟨0, by decide⟩),
   opAt 2555 (.Swap ⟨1, by decide⟩),
   opAt 2556 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2557 (.Swap ⟨0, by decide⟩),
   pushAt 2558 1 31,
   opAt 2559 .NOT,
   opAt 2560 .ADD,
   pushAt 2561 2 2111,
   opAt 2562 (.Dup ⟨1, by decide⟩),
   opAt 2563 .GT,
   pushAt 2564 2 3367,
   opAt 2565 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2590 .JUMPDEST,
   opAt 2591 (.Dup ⟨0, by decide⟩),
   opAt 2592 .MLOAD,
   pushAt 2593 2 2112,
   opAt 2594 (.Dup ⟨2, by decide⟩),
   opAt 2595 .SUB,
   opAt 2596 .MLOAD,
   opAt 2597 (.Dup ⟨1, by decide⟩),
   opAt 2598 (.Dup ⟨1, by decide⟩),
   opAt 2599 .GT,
   opAt 2600 (.Swap ⟨1, by decide⟩),
   opAt 2601 .SUB,
   opAt 2602 (.Dup ⟨3, by decide⟩),
   opAt 2603 (.Dup ⟨1, by decide⟩),
   opAt 2604 .LT,
   opAt 2605 (.Swap ⟨0, by decide⟩),
   opAt 2606 (.Dup ⟨4, by decide⟩),
   opAt 2607 (.Swap ⟨0, by decide⟩),
   opAt 2608 .SUB,
   opAt 2609 (.Dup ⟨3, by decide⟩),
   opAt 2610 .MSTORE,
   opAt 2611 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2612 (.Swap ⟨1, by decide⟩),
   opAt 2613 .POP,
   pushAt 2614 1 31,
   opAt 2615 .NOT,
   opAt 2616 .ADD,
   pushAt 2617 2 2111,
   opAt 2618 (.Dup ⟨1, by decide⟩),
   opAt 2619 .GT,
   pushAt 2620 2 3446,
   opAt 2621 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
