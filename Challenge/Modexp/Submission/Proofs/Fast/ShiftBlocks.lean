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
  [opAt 2111 .JUMPDEST,
   opAt 2112 (.Dup ⟨0, by decide⟩),
   opAt 2113 .MLOAD,
   opAt 2114 .NOT,
   opAt 2115 (.Dup ⟨2, by decide⟩),
   opAt 2116 .ADD,
   opAt 2117 (.Dup ⟨0, by decide⟩),
   opAt 2118 (.Swap ⟨2, by decide⟩),
   opAt 2119 .GT,
   opAt 2120 (.Swap ⟨1, by decide⟩),
   opAt 2121 (.Dup ⟨1, by decide⟩),
   pushAt 2122 2 1280,
   opAt 2123 .ADD,
   opAt 2124 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2125 (.Dup ⟨0, by decide⟩),
   pushAt 2126 1 31,
   opAt 2127 .NOT,
   opAt 2128 .ADD,
   opAt 2129 (.Swap ⟨0, by decide⟩),
   pushAt 2130 2 2854,
   opAt 2131 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2323 .JUMPDEST,
   pushAt 2324 2 832,
   opAt 2325 (.Dup ⟨1, by decide⟩),
   opAt 2326 .SUB,
   opAt 2327 .MLOAD,
   opAt 2328 (.Dup ⟨2, by decide⟩),
   opAt 2329 (.Dup ⟨6, by decide⟩),
   opAt 2330 (.Dup ⟨2, by decide⟩),
   opAt 2331 .MUL,
   opAt 2332 (.Swap ⟨1, by decide⟩),
   opAt 2333 (.Dup ⟨7, by decide⟩),
   opAt 2334 .MULMOD,
   opAt 2335 (.Dup ⟨1, by decide⟩),
   opAt 2336 (.Dup ⟨1, by decide⟩),
   opAt 2337 .LT,
   opAt 2338 .SUB,
   opAt 2339 (.Dup ⟨5, by decide⟩),
   opAt 2340 (.Dup ⟨2, by decide⟩),
   opAt 2341 .ADD,
   opAt 2342 (.Dup ⟨0, by decide⟩),
   opAt 2343 (.Swap ⟨6, by decide⟩),
   opAt 2344 .GT,
   opAt 2345 .SUB,
   opAt 2346 .SUB,
   opAt 2347 (.Dup ⟨4, by decide⟩),
   opAt 2348 (.Dup ⟨2, by decide⟩),
   opAt 2349 .MLOAD,
   opAt 2350 .ADD,
   opAt 2351 (.Dup ⟨0, by decide⟩),
   opAt 2352 (.Swap ⟨5, by decide⟩),
   opAt 2353 .GT,
   opAt 2354 .ADD,
   opAt 2355 (.Swap ⟨3, by decide⟩),
   opAt 2356 (.Dup ⟨1, by decide⟩),
   opAt 2357 .MSTORE,
   opAt 2358 (.Dup ⟨2, by decide⟩),
   opAt 2359 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2471 2 2080,
   opAt 2472 (.Dup ⟨1, by decide⟩),
   opAt 2473 .GT,
   pushAt 2474 2 3139,
   opAt 2475 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2514 .JUMPDEST,
   opAt 2515 (.Dup ⟨0, by decide⟩),
   opAt 2516 .MLOAD,
   opAt 2517 (.Dup ⟨1, by decide⟩),
   pushAt 2518 2 2112,
   opAt 2519 (.Swap ⟨0, by decide⟩),
   opAt 2520 .SUB,
   opAt 2521 .MLOAD,
   opAt 2522 (.Dup ⟨1, by decide⟩),
   opAt 2523 .ADD,
   opAt 2524 (.Dup ⟨0, by decide⟩),
   opAt 2525 (.Dup ⟨2, by decide⟩),
   opAt 2526 .GT,
   opAt 2527 (.Swap ⟨1, by decide⟩),
   opAt 2528 .POP,
   opAt 2529 (.Dup ⟨3, by decide⟩),
   opAt 2530 .ADD,
   opAt 2531 (.Dup ⟨0, by decide⟩),
   opAt 2532 (.Dup ⟨4, by decide⟩),
   opAt 2533 .GT,
   opAt 2534 (.Swap ⟨3, by decide⟩),
   opAt 2535 .POP,
   opAt 2536 (.Dup ⟨2, by decide⟩),
   opAt 2537 .MSTORE,
   opAt 2538 (.Swap ⟨0, by decide⟩),
   opAt 2539 (.Swap ⟨1, by decide⟩),
   opAt 2540 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2541 (.Swap ⟨0, by decide⟩),
   pushAt 2542 1 31,
   opAt 2543 .NOT,
   opAt 2544 .ADD,
   pushAt 2545 2 2111,
   opAt 2546 (.Dup ⟨1, by decide⟩),
   opAt 2547 .GT,
   pushAt 2548 2 3356,
   opAt 2549 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2574 .JUMPDEST,
   opAt 2575 (.Dup ⟨0, by decide⟩),
   opAt 2576 .MLOAD,
   pushAt 2577 2 2112,
   opAt 2578 (.Dup ⟨2, by decide⟩),
   opAt 2579 .SUB,
   opAt 2580 .MLOAD,
   opAt 2581 (.Dup ⟨1, by decide⟩),
   opAt 2582 (.Dup ⟨1, by decide⟩),
   opAt 2583 .GT,
   opAt 2584 (.Swap ⟨1, by decide⟩),
   opAt 2585 .SUB,
   opAt 2586 (.Dup ⟨3, by decide⟩),
   opAt 2587 (.Dup ⟨1, by decide⟩),
   opAt 2588 .LT,
   opAt 2589 (.Swap ⟨0, by decide⟩),
   opAt 2590 (.Dup ⟨4, by decide⟩),
   opAt 2591 (.Swap ⟨0, by decide⟩),
   opAt 2592 .SUB,
   opAt 2593 (.Dup ⟨3, by decide⟩),
   opAt 2594 .MSTORE,
   opAt 2595 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2596 (.Swap ⟨1, by decide⟩),
   opAt 2597 .POP,
   pushAt 2598 1 31,
   opAt 2599 .NOT,
   opAt 2600 .ADD,
   pushAt 2601 2 2111,
   opAt 2602 (.Dup ⟨1, by decide⟩),
   opAt 2603 .GT,
   pushAt 2604 2 3435,
   opAt 2605 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
