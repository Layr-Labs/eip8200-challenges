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
  [opAt 2124 .JUMPDEST,
   opAt 2125 (.Dup ⟨0, by decide⟩),
   opAt 2126 .MLOAD,
   opAt 2127 .NOT,
   opAt 2128 (.Dup ⟨2, by decide⟩),
   opAt 2129 .ADD,
   opAt 2130 (.Dup ⟨0, by decide⟩),
   opAt 2131 (.Swap ⟨2, by decide⟩),
   opAt 2132 .GT,
   opAt 2133 (.Swap ⟨1, by decide⟩),
   opAt 2134 (.Dup ⟨1, by decide⟩),
   pushAt 2135 2 1280,
   opAt 2136 .ADD,
   opAt 2137 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2138 (.Dup ⟨0, by decide⟩),
   pushAt 2139 1 31,
   opAt 2140 .NOT,
   opAt 2141 .ADD,
   opAt 2142 (.Swap ⟨0, by decide⟩),
   pushAt 2143 2 2859,
   opAt 2144 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2336 .JUMPDEST,
   pushAt 2337 2 832,
   opAt 2338 (.Dup ⟨1, by decide⟩),
   opAt 2339 .SUB,
   opAt 2340 .MLOAD,
   opAt 2341 (.Dup ⟨2, by decide⟩),
   opAt 2342 (.Dup ⟨6, by decide⟩),
   opAt 2343 (.Dup ⟨2, by decide⟩),
   opAt 2344 .MUL,
   opAt 2345 (.Swap ⟨1, by decide⟩),
   opAt 2346 (.Dup ⟨7, by decide⟩),
   opAt 2347 .MULMOD,
   opAt 2348 (.Dup ⟨1, by decide⟩),
   opAt 2349 (.Dup ⟨1, by decide⟩),
   opAt 2350 .LT,
   opAt 2351 .SUB,
   opAt 2352 (.Dup ⟨5, by decide⟩),
   opAt 2353 (.Dup ⟨2, by decide⟩),
   opAt 2354 .ADD,
   opAt 2355 (.Dup ⟨0, by decide⟩),
   opAt 2356 (.Swap ⟨6, by decide⟩),
   opAt 2357 .GT,
   opAt 2358 .SUB,
   opAt 2359 .SUB,
   opAt 2360 (.Dup ⟨4, by decide⟩),
   opAt 2361 (.Dup ⟨2, by decide⟩),
   opAt 2362 .MLOAD,
   opAt 2363 .ADD,
   opAt 2364 (.Dup ⟨0, by decide⟩),
   opAt 2365 (.Swap ⟨5, by decide⟩),
   opAt 2366 .GT,
   opAt 2367 .ADD,
   opAt 2368 (.Swap ⟨3, by decide⟩),
   opAt 2369 (.Dup ⟨1, by decide⟩),
   opAt 2370 .MSTORE,
   opAt 2371 (.Dup ⟨2, by decide⟩),
   opAt 2372 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2484 2 2080,
   opAt 2485 (.Dup ⟨1, by decide⟩),
   opAt 2486 .GT,
   pushAt 2487 2 3144,
   opAt 2488 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2527 .JUMPDEST,
   opAt 2528 (.Dup ⟨0, by decide⟩),
   opAt 2529 .MLOAD,
   opAt 2530 (.Dup ⟨1, by decide⟩),
   pushAt 2531 2 2112,
   opAt 2532 (.Swap ⟨0, by decide⟩),
   opAt 2533 .SUB,
   opAt 2534 .MLOAD,
   opAt 2535 (.Dup ⟨1, by decide⟩),
   opAt 2536 .ADD,
   opAt 2537 (.Dup ⟨0, by decide⟩),
   opAt 2538 (.Dup ⟨2, by decide⟩),
   opAt 2539 .GT,
   opAt 2540 (.Swap ⟨1, by decide⟩),
   opAt 2541 .POP,
   opAt 2542 (.Dup ⟨3, by decide⟩),
   opAt 2543 .ADD,
   opAt 2544 (.Dup ⟨0, by decide⟩),
   opAt 2545 (.Dup ⟨4, by decide⟩),
   opAt 2546 .GT,
   opAt 2547 (.Swap ⟨3, by decide⟩),
   opAt 2548 .POP,
   opAt 2549 (.Dup ⟨2, by decide⟩),
   opAt 2550 .MSTORE,
   opAt 2551 (.Swap ⟨0, by decide⟩),
   opAt 2552 (.Swap ⟨1, by decide⟩),
   opAt 2553 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2554 (.Swap ⟨0, by decide⟩),
   pushAt 2555 1 31,
   opAt 2556 .NOT,
   opAt 2557 .ADD,
   pushAt 2558 2 2111,
   opAt 2559 (.Dup ⟨1, by decide⟩),
   opAt 2560 .GT,
   pushAt 2561 2 3361,
   opAt 2562 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2587 .JUMPDEST,
   opAt 2588 (.Dup ⟨0, by decide⟩),
   opAt 2589 .MLOAD,
   pushAt 2590 2 2112,
   opAt 2591 (.Dup ⟨2, by decide⟩),
   opAt 2592 .SUB,
   opAt 2593 .MLOAD,
   opAt 2594 (.Dup ⟨1, by decide⟩),
   opAt 2595 (.Dup ⟨1, by decide⟩),
   opAt 2596 .GT,
   opAt 2597 (.Swap ⟨1, by decide⟩),
   opAt 2598 .SUB,
   opAt 2599 (.Dup ⟨3, by decide⟩),
   opAt 2600 (.Dup ⟨1, by decide⟩),
   opAt 2601 .LT,
   opAt 2602 (.Swap ⟨0, by decide⟩),
   opAt 2603 (.Dup ⟨4, by decide⟩),
   opAt 2604 (.Swap ⟨0, by decide⟩),
   opAt 2605 .SUB,
   opAt 2606 (.Dup ⟨3, by decide⟩),
   opAt 2607 .MSTORE,
   opAt 2608 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2609 (.Swap ⟨1, by decide⟩),
   opAt 2610 .POP,
   pushAt 2611 1 31,
   opAt 2612 .NOT,
   opAt 2613 .ADD,
   pushAt 2614 2 2111,
   opAt 2615 (.Dup ⟨1, by decide⟩),
   opAt 2616 .GT,
   pushAt 2617 2 3440,
   opAt 2618 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
