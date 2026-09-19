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
  [opAt 2100 .JUMPDEST,
   opAt 2101 (.Dup ⟨0, by decide⟩),
   opAt 2102 .MLOAD,
   opAt 2103 .NOT,
   opAt 2104 (.Dup ⟨2, by decide⟩),
   opAt 2105 .ADD,
   opAt 2106 (.Dup ⟨0, by decide⟩),
   opAt 2107 (.Swap ⟨2, by decide⟩),
   opAt 2108 .GT,
   opAt 2109 (.Swap ⟨1, by decide⟩),
   opAt 2110 (.Dup ⟨1, by decide⟩),
   pushAt 2111 2 1280,
   opAt 2112 .ADD,
   opAt 2113 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2114 (.Dup ⟨0, by decide⟩),
   pushAt 2115 1 31,
   opAt 2116 .NOT,
   opAt 2117 .ADD,
   opAt 2118 (.Swap ⟨0, by decide⟩),
   pushAt 2119 2 2592,
   opAt 2120 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2587 .JUMPDEST,
   opAt 2588 (.Dup ⟨0, by decide⟩),
   opAt 2589 .MLOAD,
   pushAt 2590 2 2112,
   opAt 2591 (.Dup ⟨2, by decide⟩),
   opAt 2592 .SUB,
   opAt 2593 .MLOAD,
   opAt 2594 (.Dup ⟨1, by decide⟩),
   opAt 2595 .ADD,
   opAt 2596 (.Swap ⟨0, by decide⟩),
   opAt 2597 (.Dup ⟨1, by decide⟩),
   opAt 2598 .LT,
   opAt 2599 (.Swap ⟨0, by decide⟩),
   opAt 2600 (.Dup ⟨3, by decide⟩),
   opAt 2601 .ADD,
   opAt 2602 (.Swap ⟨2, by decide⟩),
   opAt 2603 (.Dup ⟨3, by decide⟩),
   opAt 2604 .LT,
   opAt 2605 .OR,
   opAt 2606 (.Swap ⟨1, by decide⟩),
   opAt 2607 (.Dup ⟨1, by decide⟩),
   opAt 2608 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2609 1 31,
   opAt 2610 .NOT,
   opAt 2611 .ADD,
   pushAt 2612 2 2111,
   opAt 2613 (.Dup ⟨1, by decide⟩),
   opAt 2614 .GT,
   pushAt 2615 2 3211,
   opAt 2616 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2641 .JUMPDEST,
   opAt 2642 (.Dup ⟨0, by decide⟩),
   opAt 2643 .MLOAD,
   pushAt 2644 2 2112,
   opAt 2645 (.Dup ⟨2, by decide⟩),
   opAt 2646 .SUB,
   opAt 2647 .MLOAD,
   opAt 2648 (.Dup ⟨1, by decide⟩),
   opAt 2649 (.Dup ⟨1, by decide⟩),
   opAt 2650 .GT,
   opAt 2651 (.Swap ⟨1, by decide⟩),
   opAt 2652 .SUB,
   opAt 2653 (.Dup ⟨3, by decide⟩),
   opAt 2654 (.Dup ⟨1, by decide⟩),
   opAt 2655 .LT,
   opAt 2656 (.Swap ⟨0, by decide⟩),
   opAt 2657 (.Dup ⟨4, by decide⟩),
   opAt 2658 (.Swap ⟨0, by decide⟩),
   opAt 2659 .SUB,
   opAt 2660 (.Dup ⟨3, by decide⟩),
   opAt 2661 .MSTORE,
   opAt 2662 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2663 (.Swap ⟨1, by decide⟩),
   opAt 2664 .POP,
   pushAt 2665 1 31,
   opAt 2666 .NOT,
   opAt 2667 .ADD,
   pushAt 2668 2 2111,
   opAt 2669 (.Dup ⟨1, by decide⟩),
   opAt 2670 .GT,
   pushAt 2671 2 3284,
   opAt 2672 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
