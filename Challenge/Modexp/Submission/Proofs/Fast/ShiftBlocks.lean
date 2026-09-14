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
  [opAt 2117 .JUMPDEST,
   opAt 2118 (.Dup ⟨0, by decide⟩),
   opAt 2119 .MLOAD,
   opAt 2120 .NOT,
   opAt 2121 (.Dup ⟨2, by decide⟩),
   opAt 2122 .ADD,
   opAt 2123 (.Dup ⟨0, by decide⟩),
   opAt 2124 (.Swap ⟨2, by decide⟩),
   opAt 2125 .GT,
   opAt 2126 (.Swap ⟨1, by decide⟩),
   opAt 2127 (.Dup ⟨1, by decide⟩),
   pushAt 2128 2 1280,
   opAt 2129 .ADD,
   opAt 2130 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2131 (.Dup ⟨0, by decide⟩),
   pushAt 2132 1 31,
   opAt 2133 .NOT,
   opAt 2134 .ADD,
   opAt 2135 (.Swap ⟨0, by decide⟩),
   pushAt 2136 2 2863,
   opAt 2137 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2331 .JUMPDEST,
   pushAt 2332 2 832,
   opAt 2333 (.Dup ⟨1, by decide⟩),
   opAt 2334 .SUB,
   opAt 2335 .MLOAD,
   opAt 2336 (.Dup ⟨2, by decide⟩),
   opAt 2337 (.Dup ⟨6, by decide⟩),
   opAt 2338 (.Dup ⟨2, by decide⟩),
   opAt 2339 .MUL,
   opAt 2340 (.Swap ⟨1, by decide⟩),
   opAt 2341 (.Dup ⟨7, by decide⟩),
   opAt 2342 .MULMOD,
   opAt 2343 (.Dup ⟨1, by decide⟩),
   opAt 2344 (.Dup ⟨1, by decide⟩),
   opAt 2345 .LT,
   opAt 2346 .SUB,
   opAt 2347 (.Dup ⟨5, by decide⟩),
   opAt 2348 (.Dup ⟨2, by decide⟩),
   opAt 2349 .ADD,
   opAt 2350 (.Dup ⟨0, by decide⟩),
   opAt 2351 (.Swap ⟨6, by decide⟩),
   opAt 2352 .GT,
   opAt 2353 .SUB,
   opAt 2354 .SUB,
   opAt 2355 (.Dup ⟨4, by decide⟩),
   opAt 2356 (.Dup ⟨2, by decide⟩),
   opAt 2357 .MLOAD,
   opAt 2358 .ADD,
   opAt 2359 (.Dup ⟨0, by decide⟩),
   opAt 2360 (.Swap ⟨5, by decide⟩),
   opAt 2361 .GT,
   opAt 2362 .ADD,
   opAt 2363 (.Swap ⟨3, by decide⟩),
   opAt 2364 (.Dup ⟨1, by decide⟩),
   opAt 2365 .MSTORE,
   opAt 2366 (.Dup ⟨2, by decide⟩),
   opAt 2367 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2479 2 2080,
   opAt 2480 (.Dup ⟨1, by decide⟩),
   opAt 2481 .GT,
   pushAt 2482 2 3150,
   opAt 2483 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2523 .JUMPDEST,
   opAt 2524 (.Dup ⟨0, by decide⟩),
   opAt 2525 .MLOAD,
   opAt 2526 (.Dup ⟨1, by decide⟩),
   pushAt 2527 2 2112,
   opAt 2528 (.Swap ⟨0, by decide⟩),
   opAt 2529 .SUB,
   opAt 2530 .MLOAD,
   opAt 2531 (.Dup ⟨1, by decide⟩),
   opAt 2532 .ADD,
   opAt 2533 (.Dup ⟨0, by decide⟩),
   opAt 2534 (.Dup ⟨2, by decide⟩),
   opAt 2535 .GT,
   opAt 2536 (.Swap ⟨1, by decide⟩),
   opAt 2537 .POP,
   opAt 2538 (.Dup ⟨3, by decide⟩),
   opAt 2539 .ADD,
   opAt 2540 (.Dup ⟨0, by decide⟩),
   opAt 2541 (.Dup ⟨4, by decide⟩),
   opAt 2542 .GT,
   opAt 2543 (.Swap ⟨3, by decide⟩),
   opAt 2544 .POP,
   opAt 2545 (.Dup ⟨2, by decide⟩),
   opAt 2546 .MSTORE,
   opAt 2547 (.Swap ⟨0, by decide⟩),
   opAt 2548 (.Swap ⟨1, by decide⟩),
   opAt 2549 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2550 (.Swap ⟨0, by decide⟩),
   pushAt 2551 1 31,
   opAt 2552 .NOT,
   opAt 2553 .ADD,
   pushAt 2554 2 2111,
   opAt 2555 (.Dup ⟨1, by decide⟩),
   opAt 2556 .GT,
   pushAt 2557 2 3370,
   opAt 2558 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2583 .JUMPDEST,
   opAt 2584 (.Dup ⟨0, by decide⟩),
   opAt 2585 .MLOAD,
   pushAt 2586 2 2112,
   opAt 2587 (.Dup ⟨2, by decide⟩),
   opAt 2588 .SUB,
   opAt 2589 .MLOAD,
   opAt 2590 (.Dup ⟨1, by decide⟩),
   opAt 2591 (.Dup ⟨1, by decide⟩),
   opAt 2592 .GT,
   opAt 2593 (.Swap ⟨1, by decide⟩),
   opAt 2594 .SUB,
   opAt 2595 (.Dup ⟨3, by decide⟩),
   opAt 2596 (.Dup ⟨1, by decide⟩),
   opAt 2597 .LT,
   opAt 2598 (.Swap ⟨0, by decide⟩),
   opAt 2599 (.Dup ⟨4, by decide⟩),
   opAt 2600 (.Swap ⟨0, by decide⟩),
   opAt 2601 .SUB,
   opAt 2602 (.Dup ⟨3, by decide⟩),
   opAt 2603 .MSTORE,
   opAt 2604 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2605 (.Swap ⟨1, by decide⟩),
   opAt 2606 .POP,
   pushAt 2607 1 31,
   opAt 2608 .NOT,
   opAt 2609 .ADD,
   pushAt 2610 2 2111,
   opAt 2611 (.Dup ⟨1, by decide⟩),
   opAt 2612 .GT,
   pushAt 2613 2 3449,
   opAt 2614 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
