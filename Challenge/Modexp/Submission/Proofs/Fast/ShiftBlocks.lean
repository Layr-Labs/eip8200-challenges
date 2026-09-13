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
   pushAt 2149 2 2901,
   opAt 2150 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2327 .JUMPDEST,
   pushAt 2328 2 832,
   opAt 2329 (.Dup ⟨1, by decide⟩),
   opAt 2330 .SUB,
   opAt 2331 .MLOAD,
   opAt 2332 (.Dup ⟨2, by decide⟩),
   opAt 2333 (.Dup ⟨6, by decide⟩),
   opAt 2334 (.Dup ⟨2, by decide⟩),
   opAt 2335 .MUL,
   opAt 2336 (.Swap ⟨1, by decide⟩),
   opAt 2337 (.Dup ⟨7, by decide⟩),
   opAt 2338 .MULMOD,
   opAt 2339 (.Dup ⟨1, by decide⟩),
   opAt 2340 (.Dup ⟨1, by decide⟩),
   opAt 2341 .LT,
   opAt 2342 .SUB,
   opAt 2343 (.Dup ⟨5, by decide⟩),
   opAt 2344 (.Dup ⟨2, by decide⟩),
   opAt 2345 .ADD,
   opAt 2346 (.Dup ⟨0, by decide⟩),
   opAt 2347 (.Swap ⟨6, by decide⟩),
   opAt 2348 .GT,
   opAt 2349 .SUB,
   opAt 2350 .SUB,
   opAt 2351 (.Dup ⟨4, by decide⟩),
   opAt 2352 (.Dup ⟨2, by decide⟩),
   opAt 2353 .MLOAD,
   opAt 2354 .ADD,
   opAt 2355 (.Dup ⟨0, by decide⟩),
   opAt 2356 (.Swap ⟨5, by decide⟩),
   opAt 2357 .GT,
   opAt 2358 .ADD,
   opAt 2359 (.Swap ⟨3, by decide⟩),
   opAt 2360 (.Dup ⟨1, by decide⟩),
   opAt 2361 .MSTORE,
   opAt 2362 (.Dup ⟨2, by decide⟩),
   opAt 2363 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2475 2 2080,
   opAt 2476 (.Dup ⟨1, by decide⟩),
   opAt 2477 .GT,
   pushAt 2478 2 3164,
   opAt 2479 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2519 .JUMPDEST,
   opAt 2520 (.Dup ⟨0, by decide⟩),
   opAt 2521 .MLOAD,
   opAt 2522 .JUMPDEST,
   pushAt 2523 2 2112,
   opAt 2524 (.Dup ⟨2, by decide⟩),
   opAt 2525 .SUB,
   opAt 2526 .MLOAD,
   opAt 2527 (.Dup ⟨1, by decide⟩),
   opAt 2528 .ADD,
   opAt 2529 (.Dup ⟨0, by decide⟩),
   opAt 2530 (.Dup ⟨2, by decide⟩),
   opAt 2531 .GT,
   opAt 2532 (.Swap ⟨1, by decide⟩),
   opAt 2533 .POP,
   opAt 2534 (.Dup ⟨3, by decide⟩),
   opAt 2535 .ADD,
   opAt 2536 (.Dup ⟨0, by decide⟩),
   opAt 2537 (.Dup ⟨4, by decide⟩),
   opAt 2538 .GT,
   opAt 2539 (.Swap ⟨3, by decide⟩),
   opAt 2540 .POP,
   opAt 2541 (.Dup ⟨2, by decide⟩),
   opAt 2542 .MSTORE,
   opAt 2543 (.Swap ⟨0, by decide⟩),
   opAt 2544 (.Swap ⟨1, by decide⟩),
   opAt 2545 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2546 (.Swap ⟨0, by decide⟩),
   pushAt 2547 1 31,
   opAt 2548 .NOT,
   opAt 2549 .ADD,
   pushAt 2550 2 2111,
   opAt 2551 (.Dup ⟨1, by decide⟩),
   opAt 2552 .GT,
   pushAt 2553 2 3384,
   opAt 2554 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2579 .JUMPDEST,
   opAt 2580 (.Dup ⟨0, by decide⟩),
   opAt 2581 .MLOAD,
   pushAt 2582 2 2112,
   opAt 2583 (.Dup ⟨2, by decide⟩),
   opAt 2584 .SUB,
   opAt 2585 .MLOAD,
   opAt 2586 (.Dup ⟨1, by decide⟩),
   opAt 2587 (.Dup ⟨1, by decide⟩),
   opAt 2588 .GT,
   opAt 2589 (.Swap ⟨1, by decide⟩),
   opAt 2590 .SUB,
   opAt 2591 (.Dup ⟨3, by decide⟩),
   opAt 2592 (.Dup ⟨1, by decide⟩),
   opAt 2593 .LT,
   opAt 2594 (.Swap ⟨0, by decide⟩),
   opAt 2595 (.Dup ⟨4, by decide⟩),
   opAt 2596 (.Swap ⟨0, by decide⟩),
   opAt 2597 .SUB,
   opAt 2598 (.Dup ⟨3, by decide⟩),
   opAt 2599 .MSTORE,
   opAt 2600 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2601 (.Swap ⟨1, by decide⟩),
   opAt 2602 .POP,
   pushAt 2603 1 31,
   opAt 2604 .NOT,
   opAt 2605 .ADD,
   pushAt 2606 2 2111,
   opAt 2607 (.Dup ⟨1, by decide⟩),
   opAt 2608 .GT,
   pushAt 2609 2 3463,
   opAt 2610 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
