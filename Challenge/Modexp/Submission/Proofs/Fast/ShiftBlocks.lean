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
  [opAt 2522 .JUMPDEST,
   opAt 2523 (.Dup ⟨0, by decide⟩),
   opAt 2524 .MLOAD,
   opAt 2525 .NOT,
   opAt 2526 (.Dup ⟨2, by decide⟩),
   opAt 2527 .ADD,
   opAt 2528 (.Dup ⟨2, by decide⟩),
   opAt 2529 (.Dup ⟨1, by decide⟩),
   opAt 2530 .LT,
   opAt 2531 (.Swap ⟨2, by decide⟩),
   opAt 2532 .POP,
   opAt 2533 (.Dup ⟨1, by decide⟩),
   pushAt 2534 2 5120,
   opAt 2535 .ADD,
   opAt 2536 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2537 (.Dup ⟨0, by decide⟩),
   opAt 2538 .ISZERO,
   pushAt 2539 2 4136,
   opAt 2540 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2709 .JUMPDEST,
   opAt 2710 (.Dup ⟨0, by decide⟩),
   opAt 2711 .MLOAD,
   pushAt 2712 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2713 (.Dup ⟨5, by decide⟩),
   opAt 2714 (.Dup ⟨2, by decide⟩),
   opAt 2715 .MUL,
   opAt 2716 (.Swap ⟨1, by decide⟩),
   opAt 2717 (.Dup ⟨6, by decide⟩),
   opAt 2718 .MULMOD,
   opAt 2719 (.Dup ⟨1, by decide⟩),
   opAt 2720 (.Dup ⟨1, by decide⟩),
   opAt 2721 .LT,
   opAt 2722 .SUB,
   opAt 2723 (.Dup ⟨4, by decide⟩),
   opAt 2724 (.Dup ⟨2, by decide⟩),
   opAt 2725 .ADD,
   opAt 2726 (.Dup ⟨0, by decide⟩),
   opAt 2727 (.Swap ⟨5, by decide⟩),
   opAt 2728 .GT,
   opAt 2729 .SUB,
   opAt 2730 .SUB,
   opAt 2731 (.Dup ⟨3, by decide⟩),
   opAt 2732 (.Dup ⟨3, by decide⟩),
   opAt 2733 .MLOAD,
   opAt 2734 .ADD,
   opAt 2735 (.Dup ⟨0, by decide⟩),
   opAt 2736 (.Swap ⟨4, by decide⟩),
   opAt 2737 .GT,
   opAt 2738 .ADD,
   opAt 2739 (.Swap ⟨2, by decide⟩),
   opAt 2740 (.Dup ⟨2, by decide⟩),
   pushAt 2741 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2742 .ADD,
   opAt 2743 (.Swap ⟨2, by decide⟩),
   opAt 2744 .MSTORE,
   pushAt 2745 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2746 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2747 2 8224,
   opAt 2748 (.Dup ⟨2, by decide⟩),
   opAt 2749 .GT,
   pushAt 2750 2 4352,
   opAt 2751 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2784 .JUMPDEST,
   opAt 2785 (.Dup ⟨0, by decide⟩),
   opAt 2786 .MLOAD,
   opAt 2787 (.Dup ⟨1, by decide⟩),
   pushAt 2788 2 8256,
   opAt 2789 (.Swap ⟨0, by decide⟩),
   opAt 2790 .SUB,
   opAt 2791 .MLOAD,
   opAt 2792 (.Dup ⟨1, by decide⟩),
   opAt 2793 .ADD,
   opAt 2794 (.Dup ⟨0, by decide⟩),
   opAt 2795 (.Dup ⟨2, by decide⟩),
   opAt 2796 .GT,
   opAt 2797 (.Swap ⟨1, by decide⟩),
   opAt 2798 .POP,
   opAt 2799 (.Dup ⟨3, by decide⟩),
   opAt 2800 .ADD,
   opAt 2801 (.Dup ⟨0, by decide⟩),
   opAt 2802 (.Dup ⟨4, by decide⟩),
   opAt 2803 .GT,
   opAt 2804 (.Swap ⟨3, by decide⟩),
   opAt 2805 .POP,
   opAt 2806 (.Dup ⟨2, by decide⟩),
   opAt 2807 .MSTORE,
   opAt 2808 (.Swap ⟨0, by decide⟩),
   opAt 2809 (.Swap ⟨1, by decide⟩),
   opAt 2810 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2811 (.Swap ⟨0, by decide⟩),
   pushAt 2812 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2813 .ADD,
   pushAt 2814 2 8255,
   opAt 2815 (.Dup ⟨1, by decide⟩),
   opAt 2816 .GT,
   pushAt 2817 2 4535,
   opAt 2818 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2840 .JUMPDEST,
   opAt 2841 (.Dup ⟨0, by decide⟩),
   opAt 2842 .MLOAD,
   opAt 2843 (.Dup ⟨1, by decide⟩),
   pushAt 2844 2 8256,
   opAt 2845 (.Swap ⟨0, by decide⟩),
   opAt 2846 .SUB,
   opAt 2847 .MLOAD,
   opAt 2848 (.Dup ⟨1, by decide⟩),
   opAt 2849 (.Dup ⟨1, by decide⟩),
   opAt 2850 .GT,
   opAt 2851 (.Swap ⟨1, by decide⟩),
   opAt 2852 .SUB,
   opAt 2853 (.Dup ⟨3, by decide⟩),
   opAt 2854 (.Dup ⟨1, by decide⟩),
   opAt 2855 .LT,
   opAt 2856 (.Swap ⟨0, by decide⟩),
   opAt 2857 (.Dup ⟨4, by decide⟩),
   opAt 2858 (.Swap ⟨0, by decide⟩),
   opAt 2859 .SUB,
   opAt 2860 (.Dup ⟨3, by decide⟩),
   opAt 2861 .MSTORE,
   opAt 2862 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2863 (.Swap ⟨1, by decide⟩),
   opAt 2864 .POP,
   pushAt 2865 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2866 .ADD,
   pushAt 2867 2 8255,
   opAt 2868 (.Dup ⟨1, by decide⟩),
   opAt 2869 .GT,
   pushAt 2870 2 4641,
   opAt 2871 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
