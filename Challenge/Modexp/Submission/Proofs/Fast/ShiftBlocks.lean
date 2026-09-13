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
   opAt 2136 (.Dup ⟨2, by decide⟩),
   opAt 2137 (.Dup ⟨1, by decide⟩),
   opAt 2138 .LT,
   opAt 2139 (.Swap ⟨2, by decide⟩),
   opAt 2140 .POP,
   opAt 2141 (.Dup ⟨1, by decide⟩),
   pushAt 2142 2 1280,
   opAt 2143 .ADD,
   opAt 2144 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2145 (.Dup ⟨0, by decide⟩),
   pushAt 2146 1 31,
   opAt 2147 .NOT,
   opAt 2148 .ADD,
   opAt 2149 (.Swap ⟨0, by decide⟩),
   pushAt 2150 2 2901,
   opAt 2151 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2330 .JUMPDEST,
   pushAt 2331 2 832,
   opAt 2332 (.Dup ⟨1, by decide⟩),
   opAt 2333 .SUB,
   opAt 2334 .MLOAD,
   opAt 2335 (.Dup ⟨2, by decide⟩),
   opAt 2336 (.Dup ⟨6, by decide⟩),
   opAt 2337 (.Dup ⟨2, by decide⟩),
   opAt 2338 .MUL,
   opAt 2339 (.Swap ⟨1, by decide⟩),
   opAt 2340 (.Dup ⟨7, by decide⟩),
   opAt 2341 .MULMOD,
   opAt 2342 (.Dup ⟨1, by decide⟩),
   opAt 2343 (.Dup ⟨1, by decide⟩),
   opAt 2344 .LT,
   opAt 2345 .SUB,
   opAt 2346 (.Dup ⟨5, by decide⟩),
   opAt 2347 (.Dup ⟨2, by decide⟩),
   opAt 2348 .ADD,
   opAt 2349 (.Dup ⟨0, by decide⟩),
   opAt 2350 (.Swap ⟨6, by decide⟩),
   opAt 2351 .GT,
   opAt 2352 .SUB,
   opAt 2353 .SUB,
   opAt 2354 (.Dup ⟨4, by decide⟩),
   opAt 2355 (.Dup ⟨2, by decide⟩),
   opAt 2356 .MLOAD,
   opAt 2357 .ADD,
   opAt 2358 (.Dup ⟨0, by decide⟩),
   opAt 2359 (.Swap ⟨5, by decide⟩),
   opAt 2360 .GT,
   opAt 2361 .ADD,
   opAt 2362 (.Swap ⟨3, by decide⟩),
   opAt 2363 (.Dup ⟨1, by decide⟩),
   opAt 2364 .MSTORE,
   opAt 2365 (.Dup ⟨2, by decide⟩),
   opAt 2366 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2478 2 2080,
   opAt 2479 (.Dup ⟨1, by decide⟩),
   opAt 2480 .GT,
   pushAt 2481 2 3167,
   opAt 2482 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2522 .JUMPDEST,
   opAt 2523 (.Dup ⟨0, by decide⟩),
   opAt 2524 .MLOAD,
   opAt 2525 (.Dup ⟨1, by decide⟩),
   pushAt 2526 2 2112,
   opAt 2527 (.Swap ⟨0, by decide⟩),
   opAt 2528 .SUB,
   opAt 2529 .MLOAD,
   opAt 2530 (.Dup ⟨1, by decide⟩),
   opAt 2531 .ADD,
   opAt 2532 (.Dup ⟨0, by decide⟩),
   opAt 2533 (.Dup ⟨2, by decide⟩),
   opAt 2534 .GT,
   opAt 2535 (.Swap ⟨1, by decide⟩),
   opAt 2536 .POP,
   opAt 2537 (.Dup ⟨3, by decide⟩),
   opAt 2538 .ADD,
   opAt 2539 (.Dup ⟨0, by decide⟩),
   opAt 2540 (.Dup ⟨4, by decide⟩),
   opAt 2541 .GT,
   opAt 2542 (.Swap ⟨3, by decide⟩),
   opAt 2543 .POP,
   opAt 2544 (.Dup ⟨2, by decide⟩),
   opAt 2545 .MSTORE,
   opAt 2546 (.Swap ⟨0, by decide⟩),
   opAt 2547 (.Swap ⟨1, by decide⟩),
   opAt 2548 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2549 (.Swap ⟨0, by decide⟩),
   pushAt 2550 1 31,
   opAt 2551 .NOT,
   opAt 2552 .ADD,
   pushAt 2553 2 2111,
   opAt 2554 (.Dup ⟨1, by decide⟩),
   opAt 2555 .GT,
   pushAt 2556 2 3387,
   opAt 2557 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 .JUMPDEST,
   opAt 2583 (.Dup ⟨0, by decide⟩),
   opAt 2584 .MLOAD,
   pushAt 2585 2 2112,
   opAt 2586 (.Dup ⟨2, by decide⟩),
   opAt 2587 .SUB,
   opAt 2588 .MLOAD,
   opAt 2589 (.Dup ⟨1, by decide⟩),
   opAt 2590 (.Dup ⟨1, by decide⟩),
   opAt 2591 .GT,
   opAt 2592 (.Swap ⟨1, by decide⟩),
   opAt 2593 .SUB,
   opAt 2594 (.Dup ⟨3, by decide⟩),
   opAt 2595 (.Dup ⟨1, by decide⟩),
   opAt 2596 .LT,
   opAt 2597 (.Swap ⟨0, by decide⟩),
   opAt 2598 (.Dup ⟨4, by decide⟩),
   opAt 2599 (.Swap ⟨0, by decide⟩),
   opAt 2600 .SUB,
   opAt 2601 (.Dup ⟨3, by decide⟩),
   opAt 2602 .MSTORE,
   opAt 2603 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2604 (.Swap ⟨1, by decide⟩),
   opAt 2605 .POP,
   pushAt 2606 1 31,
   opAt 2607 .NOT,
   opAt 2608 .ADD,
   pushAt 2609 2 2111,
   opAt 2610 (.Dup ⟨1, by decide⟩),
   opAt 2611 .GT,
   pushAt 2612 2 3466,
   opAt 2613 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
