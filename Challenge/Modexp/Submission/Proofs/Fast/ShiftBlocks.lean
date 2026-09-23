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
   pushAt 2118 2 2589,
   opAt 2119 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2602 .JUMPDEST,
   opAt 2603 (.Dup ⟨0, by decide⟩),
   opAt 2604 .MLOAD,
   pushAt 2605 2 2112,
   opAt 2606 (.Dup ⟨2, by decide⟩),
   opAt 2607 .SUB,
   opAt 2608 .MLOAD,
   opAt 2609 (.Dup ⟨1, by decide⟩),
   opAt 2610 .ADD,
   opAt 2611 (.Swap ⟨0, by decide⟩),
   opAt 2612 (.Dup ⟨1, by decide⟩),
   opAt 2613 .LT,
   opAt 2614 (.Swap ⟨0, by decide⟩),
   opAt 2615 (.Dup ⟨3, by decide⟩),
   opAt 2616 .ADD,
   opAt 2617 (.Swap ⟨2, by decide⟩),
   opAt 2618 (.Dup ⟨3, by decide⟩),
   opAt 2619 .LT,
   opAt 2620 .OR,
   opAt 2621 (.Swap ⟨1, by decide⟩),
   opAt 2622 (.Dup ⟨1, by decide⟩),
   opAt 2623 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2624 1 31,
   opAt 2625 .NOT,
   opAt 2626 .ADD,
   pushAt 2627 2 2111,
   opAt 2628 (.Dup ⟨1, by decide⟩),
   opAt 2629 .GT,
   pushAt 2630 2 3220,
   opAt 2631 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2656 .JUMPDEST,
   opAt 2657 (.Dup ⟨0, by decide⟩),
   opAt 2658 .MLOAD,
   pushAt 2659 2 2112,
   opAt 2660 (.Dup ⟨2, by decide⟩),
   opAt 2661 .SUB,
   opAt 2662 .MLOAD,
   opAt 2663 (.Dup ⟨1, by decide⟩),
   opAt 2664 (.Dup ⟨1, by decide⟩),
   opAt 2665 .GT,
   opAt 2666 (.Swap ⟨1, by decide⟩),
   opAt 2667 .SUB,
   opAt 2668 (.Dup ⟨3, by decide⟩),
   opAt 2669 (.Dup ⟨1, by decide⟩),
   opAt 2670 .LT,
   opAt 2671 (.Swap ⟨0, by decide⟩),
   opAt 2672 (.Dup ⟨4, by decide⟩),
   opAt 2673 (.Swap ⟨0, by decide⟩),
   opAt 2674 .SUB,
   opAt 2675 (.Dup ⟨3, by decide⟩),
   opAt 2676 .MSTORE,
   opAt 2677 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2678 (.Swap ⟨1, by decide⟩),
   opAt 2679 .POP,
   pushAt 2680 1 31,
   opAt 2681 .NOT,
   opAt 2682 .ADD,
   pushAt 2683 2 2111,
   opAt 2684 (.Dup ⟨1, by decide⟩),
   opAt 2685 .GT,
   pushAt 2686 2 3284,
   opAt 2687 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
