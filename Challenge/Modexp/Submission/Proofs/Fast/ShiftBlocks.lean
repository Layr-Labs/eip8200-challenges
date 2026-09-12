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
  [opAt 2464 .JUMPDEST,
   opAt 2465 (.Dup ⟨0, by decide⟩),
   opAt 2466 .MLOAD,
   opAt 2467 .NOT,
   opAt 2468 (.Dup ⟨2, by decide⟩),
   opAt 2469 .ADD,
   opAt 2470 (.Dup ⟨2, by decide⟩),
   opAt 2471 (.Dup ⟨1, by decide⟩),
   opAt 2472 .LT,
   opAt 2473 (.Swap ⟨2, by decide⟩),
   opAt 2474 .POP,
   opAt 2475 (.Dup ⟨1, by decide⟩),
   pushAt 2476 2 5120,
   opAt 2477 .ADD,
   opAt 2478 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2479 (.Dup ⟨0, by decide⟩),
   opAt 2480 .ISZERO,
   pushAt 2481 2 3268,
   opAt 2482 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2655 .JUMPDEST,
   opAt 2656 (.Dup ⟨0, by decide⟩),
   opAt 2657 .MLOAD,
   pushAt 2658 0 0,
   opAt 2659 .NOT,
   opAt 2660 (.Dup ⟨5, by decide⟩),
   opAt 2661 (.Dup ⟨2, by decide⟩),
   opAt 2662 .MUL,
   opAt 2663 (.Swap ⟨1, by decide⟩),
   opAt 2664 (.Dup ⟨6, by decide⟩),
   opAt 2665 .MULMOD,
   opAt 2666 (.Dup ⟨1, by decide⟩),
   opAt 2667 (.Dup ⟨1, by decide⟩),
   opAt 2668 .LT,
   opAt 2669 .SUB,
   opAt 2670 (.Dup ⟨4, by decide⟩),
   opAt 2671 (.Dup ⟨2, by decide⟩),
   opAt 2672 .ADD,
   opAt 2673 (.Dup ⟨0, by decide⟩),
   opAt 2674 (.Swap ⟨5, by decide⟩),
   opAt 2675 .GT,
   opAt 2676 .SUB,
   opAt 2677 .SUB,
   opAt 2678 (.Dup ⟨3, by decide⟩),
   opAt 2679 (.Dup ⟨3, by decide⟩),
   opAt 2680 .MLOAD,
   opAt 2681 .ADD,
   opAt 2682 (.Dup ⟨0, by decide⟩),
   opAt 2683 (.Swap ⟨4, by decide⟩),
   opAt 2684 .GT,
   opAt 2685 .ADD,
   opAt 2686 (.Swap ⟨2, by decide⟩),
   opAt 2687 (.Dup ⟨2, by decide⟩),
   pushAt 2688 1 31,
   opAt 2689 .NOT,
   opAt 2690 .ADD,
   opAt 2691 (.Swap ⟨2, by decide⟩),
   opAt 2692 .MSTORE,
   pushAt 2693 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2694 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2695 2 8224,
   opAt 2696 (.Dup ⟨2, by decide⟩),
   opAt 2697 .GT,
   pushAt 2698 2 3491,
   opAt 2699 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2732 .JUMPDEST,
   opAt 2733 (.Dup ⟨0, by decide⟩),
   opAt 2734 .MLOAD,
   opAt 2735 (.Dup ⟨1, by decide⟩),
   pushAt 2736 2 8256,
   opAt 2737 (.Swap ⟨0, by decide⟩),
   opAt 2738 .SUB,
   opAt 2739 .MLOAD,
   opAt 2740 (.Dup ⟨1, by decide⟩),
   opAt 2741 .ADD,
   opAt 2742 (.Dup ⟨0, by decide⟩),
   opAt 2743 (.Dup ⟨2, by decide⟩),
   opAt 2744 .GT,
   opAt 2745 (.Swap ⟨1, by decide⟩),
   opAt 2746 .POP,
   opAt 2747 (.Dup ⟨3, by decide⟩),
   opAt 2748 .ADD,
   opAt 2749 (.Dup ⟨0, by decide⟩),
   opAt 2750 (.Dup ⟨4, by decide⟩),
   opAt 2751 .GT,
   opAt 2752 (.Swap ⟨3, by decide⟩),
   opAt 2753 .POP,
   opAt 2754 (.Dup ⟨2, by decide⟩),
   opAt 2755 .MSTORE,
   opAt 2756 (.Swap ⟨0, by decide⟩),
   opAt 2757 (.Swap ⟨1, by decide⟩),
   opAt 2758 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2759 (.Swap ⟨0, by decide⟩),
   pushAt 2760 1 31,
   opAt 2761 .NOT,
   opAt 2762 .ADD,
   pushAt 2763 2 8255,
   opAt 2764 (.Dup ⟨1, by decide⟩),
   opAt 2765 .GT,
   pushAt 2766 2 3613,
   opAt 2767 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2789 .JUMPDEST,
   opAt 2790 (.Dup ⟨0, by decide⟩),
   opAt 2791 .MLOAD,
   pushAt 2792 2 8256,
   opAt 2793 (.Dup ⟨2, by decide⟩),
   opAt 2794 .SUB,
   opAt 2795 .MLOAD,
   opAt 2796 (.Dup ⟨1, by decide⟩),
   opAt 2797 (.Dup ⟨1, by decide⟩),
   opAt 2798 .GT,
   opAt 2799 (.Swap ⟨1, by decide⟩),
   opAt 2800 .SUB,
   opAt 2801 (.Dup ⟨3, by decide⟩),
   opAt 2802 (.Dup ⟨1, by decide⟩),
   opAt 2803 .LT,
   opAt 2804 (.Swap ⟨0, by decide⟩),
   opAt 2805 (.Dup ⟨4, by decide⟩),
   opAt 2806 (.Swap ⟨0, by decide⟩),
   opAt 2807 .SUB,
   opAt 2808 (.Dup ⟨3, by decide⟩),
   opAt 2809 .MSTORE,
   opAt 2810 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2811 (.Swap ⟨1, by decide⟩),
   opAt 2812 .POP,
   pushAt 2813 1 31,
   opAt 2814 .NOT,
   opAt 2815 .ADD,
   pushAt 2816 2 8255,
   opAt 2817 (.Dup ⟨1, by decide⟩),
   opAt 2818 .GT,
   pushAt 2819 2 3689,
   opAt 2820 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
