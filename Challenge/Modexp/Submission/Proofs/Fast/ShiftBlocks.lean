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
  [opAt 2341 .JUMPDEST,
   pushAt 2342 2 832,
   opAt 2343 (.Dup ⟨1, by decide⟩),
   opAt 2344 .SUB,
   opAt 2345 .MLOAD,
   opAt 2346 (.Dup ⟨2, by decide⟩),
   opAt 2347 (.Dup ⟨6, by decide⟩),
   opAt 2348 (.Dup ⟨2, by decide⟩),
   opAt 2349 .MUL,
   opAt 2350 (.Swap ⟨1, by decide⟩),
   opAt 2351 (.Dup ⟨7, by decide⟩),
   opAt 2352 .MULMOD,
   opAt 2353 (.Dup ⟨1, by decide⟩),
   opAt 2354 (.Dup ⟨1, by decide⟩),
   opAt 2355 .LT,
   opAt 2356 .SUB,
   opAt 2357 (.Dup ⟨5, by decide⟩),
   opAt 2358 (.Dup ⟨2, by decide⟩),
   opAt 2359 .ADD,
   opAt 2360 (.Dup ⟨0, by decide⟩),
   opAt 2361 (.Swap ⟨6, by decide⟩),
   opAt 2362 .GT,
   opAt 2363 .SUB,
   opAt 2364 .SUB,
   opAt 2365 (.Dup ⟨4, by decide⟩),
   opAt 2366 (.Dup ⟨2, by decide⟩),
   opAt 2367 .MLOAD,
   opAt 2368 .ADD,
   opAt 2369 (.Dup ⟨0, by decide⟩),
   opAt 2370 (.Swap ⟨5, by decide⟩),
   opAt 2371 .GT,
   opAt 2372 .ADD,
   opAt 2373 (.Swap ⟨3, by decide⟩),
   opAt 2374 (.Dup ⟨1, by decide⟩),
   opAt 2375 .MSTORE,
   opAt 2376 (.Dup ⟨2, by decide⟩),
   opAt 2377 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2489 2 2080,
   opAt 2490 (.Dup ⟨1, by decide⟩),
   opAt 2491 .GT,
   pushAt 2492 2 3150,
   opAt 2493 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2533 .JUMPDEST,
   opAt 2534 (.Dup ⟨0, by decide⟩),
   opAt 2535 .MLOAD,
   opAt 2536 (.Dup ⟨1, by decide⟩),
   pushAt 2537 2 2112,
   opAt 2538 (.Swap ⟨0, by decide⟩),
   opAt 2539 .SUB,
   opAt 2540 .MLOAD,
   opAt 2541 (.Dup ⟨1, by decide⟩),
   opAt 2542 .ADD,
   opAt 2543 (.Dup ⟨0, by decide⟩),
   opAt 2544 (.Dup ⟨2, by decide⟩),
   opAt 2545 .GT,
   opAt 2546 (.Swap ⟨1, by decide⟩),
   opAt 2547 .POP,
   opAt 2548 (.Dup ⟨3, by decide⟩),
   opAt 2549 .ADD,
   opAt 2550 (.Dup ⟨0, by decide⟩),
   opAt 2551 (.Dup ⟨4, by decide⟩),
   opAt 2552 .GT,
   opAt 2553 (.Swap ⟨3, by decide⟩),
   opAt 2554 .POP,
   opAt 2555 (.Dup ⟨2, by decide⟩),
   opAt 2556 .MSTORE,
   opAt 2557 (.Swap ⟨0, by decide⟩),
   opAt 2558 (.Swap ⟨1, by decide⟩),
   opAt 2559 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2560 (.Swap ⟨0, by decide⟩),
   pushAt 2561 1 31,
   opAt 2562 .NOT,
   opAt 2563 .ADD,
   pushAt 2564 2 2111,
   opAt 2565 (.Dup ⟨1, by decide⟩),
   opAt 2566 .GT,
   pushAt 2567 2 3370,
   opAt 2568 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2593 .JUMPDEST,
   opAt 2594 (.Dup ⟨0, by decide⟩),
   opAt 2595 .MLOAD,
   pushAt 2596 2 2112,
   opAt 2597 (.Dup ⟨2, by decide⟩),
   opAt 2598 .SUB,
   opAt 2599 .MLOAD,
   opAt 2600 (.Dup ⟨1, by decide⟩),
   opAt 2601 (.Dup ⟨1, by decide⟩),
   opAt 2602 .GT,
   opAt 2603 (.Swap ⟨1, by decide⟩),
   opAt 2604 .SUB,
   opAt 2605 (.Dup ⟨3, by decide⟩),
   opAt 2606 (.Dup ⟨1, by decide⟩),
   opAt 2607 .LT,
   opAt 2608 (.Swap ⟨0, by decide⟩),
   opAt 2609 (.Dup ⟨4, by decide⟩),
   opAt 2610 (.Swap ⟨0, by decide⟩),
   opAt 2611 .SUB,
   opAt 2612 (.Dup ⟨3, by decide⟩),
   opAt 2613 .MSTORE,
   opAt 2614 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2615 (.Swap ⟨1, by decide⟩),
   opAt 2616 .POP,
   pushAt 2617 1 31,
   opAt 2618 .NOT,
   opAt 2619 .ADD,
   pushAt 2620 2 2111,
   opAt 2621 (.Dup ⟨1, by decide⟩),
   opAt 2622 .GT,
   pushAt 2623 2 3449,
   opAt 2624 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
