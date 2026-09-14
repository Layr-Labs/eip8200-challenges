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
  [opAt 2115 .JUMPDEST,
   opAt 2116 (.Dup ⟨0, by decide⟩),
   opAt 2117 .MLOAD,
   opAt 2118 .NOT,
   opAt 2119 (.Dup ⟨2, by decide⟩),
   opAt 2120 .ADD,
   opAt 2121 (.Dup ⟨0, by decide⟩),
   opAt 2122 (.Swap ⟨2, by decide⟩),
   opAt 2123 .GT,
   opAt 2124 (.Swap ⟨1, by decide⟩),
   opAt 2125 (.Dup ⟨1, by decide⟩),
   pushAt 2126 2 1280,
   opAt 2127 .ADD,
   opAt 2128 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2129 (.Dup ⟨0, by decide⟩),
   pushAt 2130 1 31,
   opAt 2131 .NOT,
   opAt 2132 .ADD,
   opAt 2133 (.Swap ⟨0, by decide⟩),
   pushAt 2134 2 2859,
   opAt 2135 .JUMPI]

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
   pushAt 2478 2 3144,
   opAt 2479 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2518 .JUMPDEST,
   opAt 2519 (.Dup ⟨0, by decide⟩),
   opAt 2520 .MLOAD,
   opAt 2521 (.Dup ⟨1, by decide⟩),
   pushAt 2522 2 2112,
   opAt 2523 (.Swap ⟨0, by decide⟩),
   opAt 2524 .SUB,
   opAt 2525 .MLOAD,
   opAt 2526 (.Dup ⟨1, by decide⟩),
   opAt 2527 .ADD,
   opAt 2528 (.Dup ⟨0, by decide⟩),
   opAt 2529 (.Dup ⟨2, by decide⟩),
   opAt 2530 .GT,
   opAt 2531 (.Swap ⟨1, by decide⟩),
   opAt 2532 .POP,
   opAt 2533 (.Dup ⟨3, by decide⟩),
   opAt 2534 .ADD,
   opAt 2535 (.Dup ⟨0, by decide⟩),
   opAt 2536 (.Dup ⟨4, by decide⟩),
   opAt 2537 .GT,
   opAt 2538 (.Swap ⟨3, by decide⟩),
   opAt 2539 .POP,
   opAt 2540 (.Dup ⟨2, by decide⟩),
   opAt 2541 .MSTORE,
   opAt 2542 (.Swap ⟨0, by decide⟩),
   opAt 2543 (.Swap ⟨1, by decide⟩),
   opAt 2544 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2545 (.Swap ⟨0, by decide⟩),
   pushAt 2546 1 31,
   opAt 2547 .NOT,
   opAt 2548 .ADD,
   pushAt 2549 2 2111,
   opAt 2550 (.Dup ⟨1, by decide⟩),
   opAt 2551 .GT,
   pushAt 2552 2 3361,
   opAt 2553 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2578 .JUMPDEST,
   opAt 2579 (.Dup ⟨0, by decide⟩),
   opAt 2580 .MLOAD,
   pushAt 2581 2 2112,
   opAt 2582 (.Dup ⟨2, by decide⟩),
   opAt 2583 .SUB,
   opAt 2584 .MLOAD,
   opAt 2585 (.Dup ⟨1, by decide⟩),
   opAt 2586 (.Dup ⟨1, by decide⟩),
   opAt 2587 .GT,
   opAt 2588 (.Swap ⟨1, by decide⟩),
   opAt 2589 .SUB,
   opAt 2590 (.Dup ⟨3, by decide⟩),
   opAt 2591 (.Dup ⟨1, by decide⟩),
   opAt 2592 .LT,
   opAt 2593 (.Swap ⟨0, by decide⟩),
   opAt 2594 (.Dup ⟨4, by decide⟩),
   opAt 2595 (.Swap ⟨0, by decide⟩),
   opAt 2596 .SUB,
   opAt 2597 (.Dup ⟨3, by decide⟩),
   opAt 2598 .MSTORE,
   opAt 2599 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2600 (.Swap ⟨1, by decide⟩),
   opAt 2601 .POP,
   pushAt 2602 1 31,
   opAt 2603 .NOT,
   opAt 2604 .ADD,
   pushAt 2605 2 2111,
   opAt 2606 (.Dup ⟨1, by decide⟩),
   opAt 2607 .GT,
   pushAt 2608 2 3440,
   opAt 2609 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
