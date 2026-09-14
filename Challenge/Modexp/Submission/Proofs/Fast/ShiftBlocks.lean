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
  [opAt 2122 .JUMPDEST,
   opAt 2123 (.Dup ⟨0, by decide⟩),
   opAt 2124 .MLOAD,
   opAt 2125 .NOT,
   opAt 2126 (.Dup ⟨2, by decide⟩),
   opAt 2127 .ADD,
   opAt 2128 (.Dup ⟨0, by decide⟩),
   opAt 2129 (.Swap ⟨2, by decide⟩),
   opAt 2130 .GT,
   opAt 2131 (.Swap ⟨1, by decide⟩),
   opAt 2132 (.Dup ⟨1, by decide⟩),
   pushAt 2133 2 1280,
   opAt 2134 .ADD,
   opAt 2135 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2136 (.Dup ⟨0, by decide⟩),
   pushAt 2137 1 31,
   opAt 2138 .NOT,
   opAt 2139 .ADD,
   opAt 2140 (.Swap ⟨0, by decide⟩),
   pushAt 2141 2 2854,
   opAt 2142 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2334 .JUMPDEST,
   pushAt 2335 2 832,
   opAt 2336 (.Dup ⟨1, by decide⟩),
   opAt 2337 .SUB,
   opAt 2338 .MLOAD,
   opAt 2339 (.Dup ⟨2, by decide⟩),
   opAt 2340 (.Dup ⟨6, by decide⟩),
   opAt 2341 (.Dup ⟨2, by decide⟩),
   opAt 2342 .MUL,
   opAt 2343 (.Swap ⟨1, by decide⟩),
   opAt 2344 (.Dup ⟨7, by decide⟩),
   opAt 2345 .MULMOD,
   opAt 2346 (.Dup ⟨1, by decide⟩),
   opAt 2347 (.Dup ⟨1, by decide⟩),
   opAt 2348 .LT,
   opAt 2349 .SUB,
   opAt 2350 (.Dup ⟨5, by decide⟩),
   opAt 2351 (.Dup ⟨2, by decide⟩),
   opAt 2352 .ADD,
   opAt 2353 (.Dup ⟨0, by decide⟩),
   opAt 2354 (.Swap ⟨6, by decide⟩),
   opAt 2355 .GT,
   opAt 2356 .SUB,
   opAt 2357 .SUB,
   opAt 2358 (.Dup ⟨4, by decide⟩),
   opAt 2359 (.Dup ⟨2, by decide⟩),
   opAt 2360 .MLOAD,
   opAt 2361 .ADD,
   opAt 2362 (.Dup ⟨0, by decide⟩),
   opAt 2363 (.Swap ⟨5, by decide⟩),
   opAt 2364 .GT,
   opAt 2365 .ADD,
   opAt 2366 (.Swap ⟨3, by decide⟩),
   opAt 2367 (.Dup ⟨1, by decide⟩),
   opAt 2368 .MSTORE,
   opAt 2369 (.Dup ⟨2, by decide⟩),
   opAt 2370 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2482 2 2080,
   opAt 2483 (.Dup ⟨1, by decide⟩),
   opAt 2484 .GT,
   pushAt 2485 2 3139,
   opAt 2486 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2525 .JUMPDEST,
   opAt 2526 (.Dup ⟨0, by decide⟩),
   opAt 2527 .MLOAD,
   opAt 2528 (.Dup ⟨1, by decide⟩),
   pushAt 2529 2 2112,
   opAt 2530 (.Swap ⟨0, by decide⟩),
   opAt 2531 .SUB,
   opAt 2532 .MLOAD,
   opAt 2533 (.Dup ⟨1, by decide⟩),
   opAt 2534 .ADD,
   opAt 2535 (.Dup ⟨0, by decide⟩),
   opAt 2536 (.Dup ⟨2, by decide⟩),
   opAt 2537 .GT,
   opAt 2538 (.Swap ⟨1, by decide⟩),
   opAt 2539 .POP,
   opAt 2540 (.Dup ⟨3, by decide⟩),
   opAt 2541 .ADD,
   opAt 2542 (.Dup ⟨0, by decide⟩),
   opAt 2543 (.Dup ⟨4, by decide⟩),
   opAt 2544 .GT,
   opAt 2545 (.Swap ⟨3, by decide⟩),
   opAt 2546 .POP,
   opAt 2547 (.Dup ⟨2, by decide⟩),
   opAt 2548 .MSTORE,
   opAt 2549 (.Swap ⟨0, by decide⟩),
   opAt 2550 (.Swap ⟨1, by decide⟩),
   opAt 2551 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2552 (.Swap ⟨0, by decide⟩),
   pushAt 2553 1 31,
   opAt 2554 .NOT,
   opAt 2555 .ADD,
   pushAt 2556 2 2111,
   opAt 2557 (.Dup ⟨1, by decide⟩),
   opAt 2558 .GT,
   pushAt 2559 2 3356,
   opAt 2560 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2585 .JUMPDEST,
   opAt 2586 (.Dup ⟨0, by decide⟩),
   opAt 2587 .MLOAD,
   pushAt 2588 2 2112,
   opAt 2589 (.Dup ⟨2, by decide⟩),
   opAt 2590 .SUB,
   opAt 2591 .MLOAD,
   opAt 2592 (.Dup ⟨1, by decide⟩),
   opAt 2593 (.Dup ⟨1, by decide⟩),
   opAt 2594 .GT,
   opAt 2595 (.Swap ⟨1, by decide⟩),
   opAt 2596 .SUB,
   opAt 2597 (.Dup ⟨3, by decide⟩),
   opAt 2598 (.Dup ⟨1, by decide⟩),
   opAt 2599 .LT,
   opAt 2600 (.Swap ⟨0, by decide⟩),
   opAt 2601 (.Dup ⟨4, by decide⟩),
   opAt 2602 (.Swap ⟨0, by decide⟩),
   opAt 2603 .SUB,
   opAt 2604 (.Dup ⟨3, by decide⟩),
   opAt 2605 .MSTORE,
   opAt 2606 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2607 (.Swap ⟨1, by decide⟩),
   opAt 2608 .POP,
   pushAt 2609 1 31,
   opAt 2610 .NOT,
   opAt 2611 .ADD,
   pushAt 2612 2 2111,
   opAt 2613 (.Dup ⟨1, by decide⟩),
   opAt 2614 .GT,
   pushAt 2615 2 3435,
   opAt 2616 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
