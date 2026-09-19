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
  [opAt 2099 .JUMPDEST,
   opAt 2100 (.Dup ⟨0, by decide⟩),
   opAt 2101 .MLOAD,
   opAt 2102 .NOT,
   opAt 2103 (.Dup ⟨2, by decide⟩),
   opAt 2104 .ADD,
   opAt 2105 (.Dup ⟨0, by decide⟩),
   opAt 2106 (.Swap ⟨2, by decide⟩),
   opAt 2107 .GT,
   opAt 2108 (.Swap ⟨1, by decide⟩),
   opAt 2109 (.Dup ⟨1, by decide⟩),
   pushAt 2110 2 1280,
   opAt 2111 .ADD,
   opAt 2112 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2113 (.Dup ⟨0, by decide⟩),
   pushAt 2114 1 31,
   opAt 2115 .NOT,
   opAt 2116 .ADD,
   opAt 2117 (.Swap ⟨0, by decide⟩),
   pushAt 2118 2 2592,
   opAt 2119 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2586 .JUMPDEST,
   opAt 2587 (.Dup ⟨0, by decide⟩),
   opAt 2588 .MLOAD,
   pushAt 2589 2 2112,
   opAt 2590 (.Dup ⟨2, by decide⟩),
   opAt 2591 .SUB,
   opAt 2592 .MLOAD,
   opAt 2593 (.Dup ⟨1, by decide⟩),
   opAt 2594 .ADD,
   opAt 2595 (.Swap ⟨0, by decide⟩),
   opAt 2596 (.Dup ⟨1, by decide⟩),
   opAt 2597 .LT,
   opAt 2598 (.Swap ⟨0, by decide⟩),
   opAt 2599 (.Dup ⟨3, by decide⟩),
   opAt 2600 .ADD,
   opAt 2601 (.Swap ⟨2, by decide⟩),
   opAt 2602 (.Dup ⟨3, by decide⟩),
   opAt 2603 .LT,
   opAt 2604 .OR,
   opAt 2605 (.Swap ⟨1, by decide⟩),
   opAt 2606 (.Dup ⟨1, by decide⟩),
   opAt 2607 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2608 1 31,
   opAt 2609 .NOT,
   opAt 2610 .ADD,
   pushAt 2611 2 2111,
   opAt 2612 (.Dup ⟨1, by decide⟩),
   opAt 2613 .GT,
   pushAt 2614 2 3211,
   opAt 2615 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2640 .JUMPDEST,
   opAt 2641 (.Dup ⟨0, by decide⟩),
   opAt 2642 .MLOAD,
   pushAt 2643 2 2112,
   opAt 2644 (.Dup ⟨2, by decide⟩),
   opAt 2645 .SUB,
   opAt 2646 .MLOAD,
   opAt 2647 (.Dup ⟨1, by decide⟩),
   opAt 2648 (.Dup ⟨1, by decide⟩),
   opAt 2649 .GT,
   opAt 2650 (.Swap ⟨1, by decide⟩),
   opAt 2651 .SUB,
   opAt 2652 (.Dup ⟨3, by decide⟩),
   opAt 2653 (.Dup ⟨1, by decide⟩),
   opAt 2654 .LT,
   opAt 2655 (.Swap ⟨0, by decide⟩),
   opAt 2656 (.Dup ⟨4, by decide⟩),
   opAt 2657 (.Swap ⟨0, by decide⟩),
   opAt 2658 .SUB,
   opAt 2659 (.Dup ⟨3, by decide⟩),
   opAt 2660 .MSTORE,
   opAt 2661 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2662 (.Swap ⟨1, by decide⟩),
   opAt 2663 .POP,
   pushAt 2664 1 31,
   opAt 2665 .NOT,
   opAt 2666 .ADD,
   pushAt 2667 2 2111,
   opAt 2668 (.Dup ⟨1, by decide⟩),
   opAt 2669 .GT,
   pushAt 2670 2 3284,
   opAt 2671 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
