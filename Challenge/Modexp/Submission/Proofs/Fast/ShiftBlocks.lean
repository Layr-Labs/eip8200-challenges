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
  [opAt 2583 .JUMPDEST,
   opAt 2584 (.Dup ⟨0, by decide⟩),
   opAt 2585 .MLOAD,
   opAt 2586 .NOT,
   opAt 2587 (.Dup ⟨2, by decide⟩),
   opAt 2588 .ADD,
   opAt 2589 (.Dup ⟨2, by decide⟩),
   opAt 2590 (.Dup ⟨1, by decide⟩),
   opAt 2591 .LT,
   opAt 2592 (.Swap ⟨2, by decide⟩),
   opAt 2593 .POP,
   opAt 2594 (.Dup ⟨1, by decide⟩),
   pushAt 2595 2 5120,
   opAt 2596 .ADD,
   opAt 2597 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2598 (.Dup ⟨0, by decide⟩),
   opAt 2599 .ISZERO,
   pushAt 2600 2 3424,
   opAt 2601 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2774 .JUMPDEST,
   opAt 2775 (.Dup ⟨0, by decide⟩),
   opAt 2776 .MLOAD,
   pushAt 2777 0 0,
   opAt 2778 .NOT,
   opAt 2779 (.Dup ⟨5, by decide⟩),
   opAt 2780 (.Dup ⟨2, by decide⟩),
   opAt 2781 .MUL,
   opAt 2782 (.Swap ⟨1, by decide⟩),
   opAt 2783 (.Dup ⟨6, by decide⟩),
   opAt 2784 .MULMOD,
   opAt 2785 (.Dup ⟨1, by decide⟩),
   opAt 2786 (.Dup ⟨1, by decide⟩),
   opAt 2787 .LT,
   opAt 2788 .SUB,
   opAt 2789 (.Dup ⟨4, by decide⟩),
   opAt 2790 (.Dup ⟨2, by decide⟩),
   opAt 2791 .ADD,
   opAt 2792 (.Dup ⟨0, by decide⟩),
   opAt 2793 (.Swap ⟨5, by decide⟩),
   opAt 2794 .GT,
   opAt 2795 .SUB,
   opAt 2796 .SUB,
   opAt 2797 (.Dup ⟨3, by decide⟩),
   opAt 2798 (.Dup ⟨3, by decide⟩),
   opAt 2799 .MLOAD,
   opAt 2800 .ADD,
   opAt 2801 (.Dup ⟨0, by decide⟩),
   opAt 2802 (.Swap ⟨4, by decide⟩),
   opAt 2803 .GT,
   opAt 2804 .ADD,
   opAt 2805 (.Swap ⟨2, by decide⟩),
   opAt 2806 (.Dup ⟨2, by decide⟩),
   pushAt 2807 1 31,
   opAt 2808 .NOT,
   opAt 2809 .ADD,
   opAt 2810 (.Swap ⟨2, by decide⟩),
   opAt 2811 .MSTORE,
   pushAt 2812 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2813 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2814 2 8224,
   opAt 2815 (.Dup ⟨2, by decide⟩),
   opAt 2816 .GT,
   pushAt 2817 2 3647,
   opAt 2818 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2851 .JUMPDEST,
   opAt 2852 (.Dup ⟨0, by decide⟩),
   opAt 2853 .MLOAD,
   opAt 2854 (.Dup ⟨1, by decide⟩),
   pushAt 2855 2 8256,
   opAt 2856 (.Swap ⟨0, by decide⟩),
   opAt 2857 .SUB,
   opAt 2858 .MLOAD,
   opAt 2859 (.Dup ⟨1, by decide⟩),
   opAt 2860 .ADD,
   opAt 2861 (.Dup ⟨0, by decide⟩),
   opAt 2862 (.Dup ⟨2, by decide⟩),
   opAt 2863 .GT,
   opAt 2864 (.Swap ⟨1, by decide⟩),
   opAt 2865 .POP,
   opAt 2866 (.Dup ⟨3, by decide⟩),
   opAt 2867 .ADD,
   opAt 2868 (.Dup ⟨0, by decide⟩),
   opAt 2869 (.Dup ⟨4, by decide⟩),
   opAt 2870 .GT,
   opAt 2871 (.Swap ⟨3, by decide⟩),
   opAt 2872 .POP,
   opAt 2873 (.Dup ⟨2, by decide⟩),
   opAt 2874 .MSTORE,
   opAt 2875 (.Swap ⟨0, by decide⟩),
   opAt 2876 (.Swap ⟨1, by decide⟩),
   opAt 2877 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2878 (.Swap ⟨0, by decide⟩),
   pushAt 2879 1 31,
   opAt 2880 .NOT,
   opAt 2881 .ADD,
   pushAt 2882 2 8255,
   opAt 2883 (.Dup ⟨1, by decide⟩),
   opAt 2884 .GT,
   pushAt 2885 2 3769,
   opAt 2886 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2908 .JUMPDEST,
   opAt 2909 (.Dup ⟨0, by decide⟩),
   opAt 2910 .MLOAD,
   pushAt 2911 2 8256,
   opAt 2912 (.Dup ⟨2, by decide⟩),
   opAt 2913 .SUB,
   opAt 2914 .MLOAD,
   opAt 2915 (.Dup ⟨1, by decide⟩),
   opAt 2916 (.Dup ⟨1, by decide⟩),
   opAt 2917 .GT,
   opAt 2918 (.Swap ⟨1, by decide⟩),
   opAt 2919 .SUB,
   opAt 2920 (.Dup ⟨3, by decide⟩),
   opAt 2921 (.Dup ⟨1, by decide⟩),
   opAt 2922 .LT,
   opAt 2923 (.Swap ⟨0, by decide⟩),
   opAt 2924 (.Dup ⟨4, by decide⟩),
   opAt 2925 (.Swap ⟨0, by decide⟩),
   opAt 2926 .SUB,
   opAt 2927 (.Dup ⟨3, by decide⟩),
   opAt 2928 .MSTORE,
   opAt 2929 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2930 (.Swap ⟨1, by decide⟩),
   opAt 2931 .POP,
   pushAt 2932 1 31,
   opAt 2933 .NOT,
   opAt 2934 .ADD,
   pushAt 2935 2 8255,
   opAt 2936 (.Dup ⟨1, by decide⟩),
   opAt 2937 .GT,
   pushAt 2938 2 3845,
   opAt 2939 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
