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
  [opAt 2080 .JUMPDEST,
   opAt 2081 (.Dup ⟨0, by decide⟩),
   opAt 2082 .MLOAD,
   opAt 2083 .NOT,
   opAt 2084 (.Dup ⟨2, by decide⟩),
   opAt 2085 .ADD,
   opAt 2086 (.Dup ⟨0, by decide⟩),
   opAt 2087 (.Swap ⟨2, by decide⟩),
   opAt 2088 .GT,
   opAt 2089 (.Swap ⟨1, by decide⟩),
   opAt 2090 (.Dup ⟨1, by decide⟩),
   pushAt 2091 2 1280,
   opAt 2092 .ADD,
   opAt 2093 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2094 (.Dup ⟨0, by decide⟩),
   pushAt 2095 1 31,
   opAt 2096 .NOT,
   opAt 2097 .ADD,
   opAt 2098 (.Swap ⟨0, by decide⟩),
   pushAt 2099 2 2523,
   opAt 2100 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2567 .JUMPDEST,
   opAt 2568 (.Dup ⟨0, by decide⟩),
   opAt 2569 .MLOAD,
   pushAt 2570 3 2112,
   opAt 2571 (.Dup ⟨2, by decide⟩),
   opAt 2572 .SUB,
   opAt 2573 .MLOAD,
   opAt 2574 (.Dup ⟨1, by decide⟩),
   opAt 2575 .ADD,
   opAt 2576 (.Swap ⟨0, by decide⟩),
   opAt 2577 (.Dup ⟨1, by decide⟩),
   opAt 2578 .LT,
   opAt 2579 (.Swap ⟨0, by decide⟩),
   opAt 2580 (.Dup ⟨3, by decide⟩),
   opAt 2581 .ADD,
   opAt 2582 (.Swap ⟨2, by decide⟩),
   opAt 2583 (.Dup ⟨3, by decide⟩),
   opAt 2584 .LT,
   opAt 2585 .OR,
   opAt 2586 (.Swap ⟨1, by decide⟩),
   opAt 2587 (.Dup ⟨1, by decide⟩),
   opAt 2588 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2589 1 31,
   opAt 2590 .NOT,
   opAt 2591 .ADD,
   pushAt 2592 2 2111,
   opAt 2593 (.Dup ⟨1, by decide⟩),
   opAt 2594 .GT,
   pushAt 2595 2 3142,
   opAt 2596 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2597 .JUMPDEST,
   opAt 2598 .JUMPDEST,
   opAt 2599 .JUMPDEST,
   opAt 2600 .JUMPDEST,
   opAt 2601 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2626 .JUMPDEST,
   opAt 2627 (.Dup ⟨0, by decide⟩),
   opAt 2628 .MLOAD,
   pushAt 2629 2 2112,
   opAt 2630 (.Dup ⟨2, by decide⟩),
   opAt 2631 .SUB,
   opAt 2632 .MLOAD,
   opAt 2633 (.Dup ⟨1, by decide⟩),
   opAt 2634 (.Dup ⟨1, by decide⟩),
   opAt 2635 .GT,
   opAt 2636 (.Swap ⟨1, by decide⟩),
   opAt 2637 .SUB,
   opAt 2638 (.Dup ⟨3, by decide⟩),
   opAt 2639 (.Dup ⟨1, by decide⟩),
   opAt 2640 .LT,
   opAt 2641 (.Swap ⟨0, by decide⟩),
   opAt 2642 (.Dup ⟨4, by decide⟩),
   opAt 2643 (.Swap ⟨0, by decide⟩),
   opAt 2644 .SUB,
   opAt 2645 (.Dup ⟨3, by decide⟩),
   opAt 2646 .MSTORE,
   opAt 2647 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2648 (.Swap ⟨1, by decide⟩),
   opAt 2649 .POP,
   pushAt 2650 1 31,
   opAt 2651 .NOT,
   opAt 2652 .ADD,
   pushAt 2653 2 2111,
   opAt 2654 (.Dup ⟨1, by decide⟩),
   opAt 2655 .GT,
   pushAt 2656 2 3221,
   opAt 2657 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
