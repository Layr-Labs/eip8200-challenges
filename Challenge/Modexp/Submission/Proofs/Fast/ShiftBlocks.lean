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
  [opAt 2772 .JUMPDEST,
   opAt 2773 (.Dup ⟨0, by decide⟩),
   opAt 2774 .MLOAD,
   pushAt 2775 0 0,
   opAt 2776 .NOT,
   opAt 2777 (.Dup ⟨5, by decide⟩),
   opAt 2778 (.Dup ⟨2, by decide⟩),
   opAt 2779 .MUL,
   opAt 2780 (.Swap ⟨1, by decide⟩),
   opAt 2781 (.Dup ⟨6, by decide⟩),
   opAt 2782 .MULMOD,
   opAt 2783 (.Dup ⟨1, by decide⟩),
   opAt 2784 (.Dup ⟨1, by decide⟩),
   opAt 2785 .LT,
   opAt 2786 .SUB,
   opAt 2787 (.Dup ⟨4, by decide⟩),
   opAt 2788 (.Dup ⟨2, by decide⟩),
   opAt 2789 .ADD,
   opAt 2790 (.Dup ⟨0, by decide⟩),
   opAt 2791 (.Swap ⟨5, by decide⟩),
   opAt 2792 .GT,
   opAt 2793 .SUB,
   opAt 2794 .SUB,
   opAt 2795 (.Dup ⟨3, by decide⟩),
   opAt 2796 (.Dup ⟨3, by decide⟩),
   opAt 2797 .MLOAD,
   opAt 2798 .ADD,
   opAt 2799 (.Dup ⟨0, by decide⟩),
   opAt 2800 (.Swap ⟨4, by decide⟩),
   opAt 2801 .GT,
   opAt 2802 .ADD,
   opAt 2803 (.Swap ⟨2, by decide⟩),
   opAt 2804 (.Dup ⟨2, by decide⟩),
   pushAt 2805 1 31,
   opAt 2806 .NOT,
   opAt 2807 .ADD,
   opAt 2808 (.Swap ⟨2, by decide⟩),
   opAt 2809 .MSTORE,
   pushAt 2810 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2811 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2812 2 8224,
   opAt 2813 (.Dup ⟨2, by decide⟩),
   opAt 2814 .GT,
   pushAt 2815 2 3643,
   opAt 2816 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2849 .JUMPDEST,
   opAt 2850 (.Dup ⟨0, by decide⟩),
   opAt 2851 .MLOAD,
   opAt 2852 (.Dup ⟨1, by decide⟩),
   pushAt 2853 2 8256,
   opAt 2854 (.Swap ⟨0, by decide⟩),
   opAt 2855 .SUB,
   opAt 2856 .MLOAD,
   opAt 2857 (.Dup ⟨1, by decide⟩),
   opAt 2858 .ADD,
   opAt 2859 (.Dup ⟨0, by decide⟩),
   opAt 2860 (.Dup ⟨2, by decide⟩),
   opAt 2861 .GT,
   opAt 2862 (.Swap ⟨1, by decide⟩),
   opAt 2863 .POP,
   opAt 2864 (.Dup ⟨3, by decide⟩),
   opAt 2865 .ADD,
   opAt 2866 (.Dup ⟨0, by decide⟩),
   opAt 2867 (.Dup ⟨4, by decide⟩),
   opAt 2868 .GT,
   opAt 2869 (.Swap ⟨3, by decide⟩),
   opAt 2870 .POP,
   opAt 2871 (.Dup ⟨2, by decide⟩),
   opAt 2872 .MSTORE,
   opAt 2873 (.Swap ⟨0, by decide⟩),
   opAt 2874 (.Swap ⟨1, by decide⟩),
   opAt 2875 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2876 (.Swap ⟨0, by decide⟩),
   pushAt 2877 1 31,
   opAt 2878 .NOT,
   opAt 2879 .ADD,
   pushAt 2880 2 8255,
   opAt 2881 (.Dup ⟨1, by decide⟩),
   opAt 2882 .GT,
   pushAt 2883 2 3765,
   opAt 2884 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2906 .JUMPDEST,
   opAt 2907 (.Dup ⟨0, by decide⟩),
   opAt 2908 .MLOAD,
   pushAt 2909 2 8256,
   opAt 2910 (.Dup ⟨2, by decide⟩),
   opAt 2911 .SUB,
   opAt 2912 .MLOAD,
   opAt 2913 (.Dup ⟨1, by decide⟩),
   opAt 2914 (.Dup ⟨1, by decide⟩),
   opAt 2915 .GT,
   opAt 2916 (.Swap ⟨1, by decide⟩),
   opAt 2917 .SUB,
   opAt 2918 (.Dup ⟨3, by decide⟩),
   opAt 2919 (.Dup ⟨1, by decide⟩),
   opAt 2920 .LT,
   opAt 2921 (.Swap ⟨0, by decide⟩),
   opAt 2922 (.Dup ⟨4, by decide⟩),
   opAt 2923 (.Swap ⟨0, by decide⟩),
   opAt 2924 .SUB,
   opAt 2925 (.Dup ⟨3, by decide⟩),
   opAt 2926 .MSTORE,
   opAt 2927 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2928 (.Swap ⟨1, by decide⟩),
   opAt 2929 .POP,
   pushAt 2930 1 31,
   opAt 2931 .NOT,
   opAt 2932 .ADD,
   pushAt 2933 2 8255,
   opAt 2934 (.Dup ⟨1, by decide⟩),
   opAt 2935 .GT,
   pushAt 2936 2 3841,
   opAt 2937 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
