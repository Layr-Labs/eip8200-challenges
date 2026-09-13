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
  [opAt 2137 .JUMPDEST,
   opAt 2138 (.Dup ⟨0, by decide⟩),
   opAt 2139 .MLOAD,
   opAt 2140 .NOT,
   opAt 2141 (.Dup ⟨2, by decide⟩),
   opAt 2142 .ADD,
   opAt 2143 (.Dup ⟨2, by decide⟩),
   opAt 2144 (.Dup ⟨1, by decide⟩),
   opAt 2145 .LT,
   opAt 2146 (.Swap ⟨2, by decide⟩),
   opAt 2147 .POP,
   opAt 2148 (.Dup ⟨1, by decide⟩),
   pushAt 2149 2 1280,
   opAt 2150 .ADD,
   opAt 2151 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2152 (.Dup ⟨0, by decide⟩),
   pushAt 2153 1 31,
   opAt 2154 .NOT,
   opAt 2155 .ADD,
   opAt 2156 (.Swap ⟨0, by decide⟩),
   pushAt 2157 2 2908,
   opAt 2158 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2342 .JUMPDEST,
   opAt 2343 (.Dup ⟨0, by decide⟩),
   opAt 2344 .MLOAD,
   pushAt 2345 0 0,
   opAt 2346 .NOT,
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
   opAt 2366 (.Dup ⟨3, by decide⟩),
   opAt 2367 .MLOAD,
   opAt 2368 .ADD,
   opAt 2369 (.Dup ⟨0, by decide⟩),
   opAt 2370 (.Swap ⟨5, by decide⟩),
   opAt 2371 .GT,
   opAt 2372 .ADD,
   opAt 2373 (.Swap ⟨3, by decide⟩),
   opAt 2374 (.Dup ⟨2, by decide⟩),
   opAt 2375 (.Dup ⟨4, by decide⟩),
   opAt 2376 .ADD,
   opAt 2377 (.Swap ⟨2, by decide⟩),
   opAt 2378 .MSTORE,
   opAt 2379 (.Dup ⟨2, by decide⟩),
   opAt 2380 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2498 2 2080,
   opAt 2499 (.Dup ⟨2, by decide⟩),
   opAt 2500 .GT,
   pushAt 2501 2 3183,
   opAt 2502 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2542 .JUMPDEST,
   opAt 2543 (.Dup ⟨0, by decide⟩),
   opAt 2544 .MLOAD,
   opAt 2545 (.Dup ⟨1, by decide⟩),
   pushAt 2546 2 2112,
   opAt 2547 (.Swap ⟨0, by decide⟩),
   opAt 2548 .SUB,
   opAt 2549 .MLOAD,
   opAt 2550 (.Dup ⟨1, by decide⟩),
   opAt 2551 .ADD,
   opAt 2552 (.Dup ⟨0, by decide⟩),
   opAt 2553 (.Dup ⟨2, by decide⟩),
   opAt 2554 .GT,
   opAt 2555 (.Swap ⟨1, by decide⟩),
   opAt 2556 .POP,
   opAt 2557 (.Dup ⟨3, by decide⟩),
   opAt 2558 .ADD,
   opAt 2559 (.Dup ⟨0, by decide⟩),
   opAt 2560 (.Dup ⟨4, by decide⟩),
   opAt 2561 .GT,
   opAt 2562 (.Swap ⟨3, by decide⟩),
   opAt 2563 .POP,
   opAt 2564 (.Dup ⟨2, by decide⟩),
   opAt 2565 .MSTORE,
   opAt 2566 (.Swap ⟨0, by decide⟩),
   opAt 2567 (.Swap ⟨1, by decide⟩),
   opAt 2568 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2569 (.Swap ⟨0, by decide⟩),
   pushAt 2570 1 31,
   opAt 2571 .NOT,
   opAt 2572 .ADD,
   pushAt 2573 2 2111,
   opAt 2574 (.Dup ⟨1, by decide⟩),
   opAt 2575 .GT,
   pushAt 2576 2 3403,
   opAt 2577 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2602 .JUMPDEST,
   opAt 2603 (.Dup ⟨0, by decide⟩),
   opAt 2604 .MLOAD,
   pushAt 2605 2 2112,
   opAt 2606 (.Dup ⟨2, by decide⟩),
   opAt 2607 .SUB,
   opAt 2608 .MLOAD,
   opAt 2609 (.Dup ⟨1, by decide⟩),
   opAt 2610 (.Dup ⟨1, by decide⟩),
   opAt 2611 .GT,
   opAt 2612 (.Swap ⟨1, by decide⟩),
   opAt 2613 .SUB,
   opAt 2614 (.Dup ⟨3, by decide⟩),
   opAt 2615 (.Dup ⟨1, by decide⟩),
   opAt 2616 .LT,
   opAt 2617 (.Swap ⟨0, by decide⟩),
   opAt 2618 (.Dup ⟨4, by decide⟩),
   opAt 2619 (.Swap ⟨0, by decide⟩),
   opAt 2620 .SUB,
   opAt 2621 (.Dup ⟨3, by decide⟩),
   opAt 2622 .MSTORE,
   opAt 2623 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2624 (.Swap ⟨1, by decide⟩),
   opAt 2625 .POP,
   pushAt 2626 1 31,
   opAt 2627 .NOT,
   opAt 2628 .ADD,
   pushAt 2629 2 2111,
   opAt 2630 (.Dup ⟨1, by decide⟩),
   opAt 2631 .GT,
   pushAt 2632 2 3482,
   opAt 2633 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
