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
  [opAt 2102 .JUMPDEST,
   opAt 2103 (.Dup ⟨0, by decide⟩),
   opAt 2104 .MLOAD,
   opAt 2105 .NOT,
   opAt 2106 (.Dup ⟨2, by decide⟩),
   opAt 2107 .ADD,
   opAt 2108 (.Dup ⟨0, by decide⟩),
   opAt 2109 (.Swap ⟨2, by decide⟩),
   opAt 2110 .GT,
   opAt 2111 (.Swap ⟨1, by decide⟩),
   opAt 2112 (.Dup ⟨1, by decide⟩),
   pushAt 2113 2 1280,
   opAt 2114 .ADD,
   opAt 2115 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2116 (.Dup ⟨0, by decide⟩),
   pushAt 2117 1 31,
   opAt 2118 .NOT,
   opAt 2119 .ADD,
   opAt 2120 (.Swap ⟨0, by decide⟩),
   pushAt 2121 2 2592,
   opAt 2122 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2589 .JUMPDEST,
   opAt 2590 (.Dup ⟨0, by decide⟩),
   opAt 2591 .MLOAD,
   pushAt 2592 2 2112,
   opAt 2593 (.Dup ⟨2, by decide⟩),
   opAt 2594 .SUB,
   opAt 2595 .MLOAD,
   opAt 2596 (.Dup ⟨1, by decide⟩),
   opAt 2597 .ADD,
   opAt 2598 (.Swap ⟨0, by decide⟩),
   opAt 2599 (.Dup ⟨1, by decide⟩),
   opAt 2600 .LT,
   opAt 2601 (.Swap ⟨0, by decide⟩),
   opAt 2602 (.Dup ⟨3, by decide⟩),
   opAt 2603 .ADD,
   opAt 2604 (.Swap ⟨2, by decide⟩),
   opAt 2605 (.Dup ⟨3, by decide⟩),
   opAt 2606 .LT,
   opAt 2607 .OR,
   opAt 2608 (.Swap ⟨1, by decide⟩),
   opAt 2609 (.Dup ⟨1, by decide⟩),
   opAt 2610 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2611 1 31,
   opAt 2612 .NOT,
   opAt 2613 .ADD,
   pushAt 2614 2 2111,
   opAt 2615 (.Dup ⟨1, by decide⟩),
   opAt 2616 .GT,
   pushAt 2617 2 3211,
   opAt 2618 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2643 .JUMPDEST,
   opAt 2644 (.Dup ⟨0, by decide⟩),
   opAt 2645 .MLOAD,
   pushAt 2646 2 2112,
   opAt 2647 (.Dup ⟨2, by decide⟩),
   opAt 2648 .SUB,
   opAt 2649 .MLOAD,
   opAt 2650 (.Dup ⟨1, by decide⟩),
   opAt 2651 (.Dup ⟨1, by decide⟩),
   opAt 2652 .GT,
   opAt 2653 (.Swap ⟨1, by decide⟩),
   opAt 2654 .SUB,
   opAt 2655 (.Dup ⟨3, by decide⟩),
   opAt 2656 (.Dup ⟨1, by decide⟩),
   opAt 2657 .LT,
   opAt 2658 (.Swap ⟨0, by decide⟩),
   opAt 2659 (.Dup ⟨4, by decide⟩),
   opAt 2660 (.Swap ⟨0, by decide⟩),
   opAt 2661 .SUB,
   opAt 2662 (.Dup ⟨3, by decide⟩),
   opAt 2663 .MSTORE,
   opAt 2664 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2665 (.Swap ⟨1, by decide⟩),
   opAt 2666 .POP,
   pushAt 2667 1 31,
   opAt 2668 .NOT,
   opAt 2669 .ADD,
   pushAt 2670 2 2111,
   opAt 2671 (.Dup ⟨1, by decide⟩),
   opAt 2672 .GT,
   pushAt 2673 2 3284,
   opAt 2674 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
