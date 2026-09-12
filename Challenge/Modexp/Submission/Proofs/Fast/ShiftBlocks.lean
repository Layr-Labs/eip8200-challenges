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
  [opAt 2643 .JUMPDEST,
   opAt 2644 (.Dup ⟨0, by decide⟩),
   opAt 2645 .MLOAD,
   opAt 2646 .NOT,
   opAt 2647 (.Dup ⟨2, by decide⟩),
   opAt 2648 .ADD,
   opAt 2649 (.Dup ⟨2, by decide⟩),
   opAt 2650 (.Dup ⟨1, by decide⟩),
   opAt 2651 .LT,
   opAt 2652 (.Swap ⟨2, by decide⟩),
   opAt 2653 .POP,
   opAt 2654 (.Dup ⟨1, by decide⟩),
   pushAt 2655 2 5120,
   opAt 2656 .ADD,
   opAt 2657 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2658 (.Dup ⟨0, by decide⟩),
   opAt 2659 .ISZERO,
   pushAt 2660 2 3536,
   opAt 2661 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2834 .JUMPDEST,
   opAt 2835 (.Dup ⟨0, by decide⟩),
   opAt 2836 .MLOAD,
   pushAt 2837 0 0,
   opAt 2838 .NOT,
   opAt 2839 (.Dup ⟨5, by decide⟩),
   opAt 2840 (.Dup ⟨2, by decide⟩),
   opAt 2841 .MUL,
   opAt 2842 (.Swap ⟨1, by decide⟩),
   opAt 2843 (.Dup ⟨6, by decide⟩),
   opAt 2844 .MULMOD,
   opAt 2845 (.Dup ⟨1, by decide⟩),
   opAt 2846 (.Dup ⟨1, by decide⟩),
   opAt 2847 .LT,
   opAt 2848 .SUB,
   opAt 2849 (.Dup ⟨4, by decide⟩),
   opAt 2850 (.Dup ⟨2, by decide⟩),
   opAt 2851 .ADD,
   opAt 2852 (.Dup ⟨0, by decide⟩),
   opAt 2853 (.Swap ⟨5, by decide⟩),
   opAt 2854 .GT,
   opAt 2855 .SUB,
   opAt 2856 .SUB,
   opAt 2857 (.Dup ⟨3, by decide⟩),
   opAt 2858 (.Dup ⟨3, by decide⟩),
   opAt 2859 .MLOAD,
   opAt 2860 .ADD,
   opAt 2861 (.Dup ⟨0, by decide⟩),
   opAt 2862 (.Swap ⟨4, by decide⟩),
   opAt 2863 .GT,
   opAt 2864 .ADD,
   opAt 2865 (.Swap ⟨2, by decide⟩),
   opAt 2866 (.Dup ⟨2, by decide⟩),
   pushAt 2867 1 31,
   opAt 2868 .NOT,
   opAt 2869 .ADD,
   opAt 2870 (.Swap ⟨2, by decide⟩),
   opAt 2871 .MSTORE,
   pushAt 2872 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2873 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2874 2 8224,
   opAt 2875 (.Dup ⟨2, by decide⟩),
   opAt 2876 .GT,
   pushAt 2877 2 3759,
   opAt 2878 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2911 .JUMPDEST,
   opAt 2912 (.Dup ⟨0, by decide⟩),
   opAt 2913 .MLOAD,
   opAt 2914 (.Dup ⟨1, by decide⟩),
   pushAt 2915 2 8256,
   opAt 2916 (.Swap ⟨0, by decide⟩),
   opAt 2917 .SUB,
   opAt 2918 .MLOAD,
   opAt 2919 (.Dup ⟨1, by decide⟩),
   opAt 2920 .ADD,
   opAt 2921 (.Dup ⟨0, by decide⟩),
   opAt 2922 (.Dup ⟨2, by decide⟩),
   opAt 2923 .GT,
   opAt 2924 (.Swap ⟨1, by decide⟩),
   opAt 2925 .POP,
   opAt 2926 (.Dup ⟨3, by decide⟩),
   opAt 2927 .ADD,
   opAt 2928 (.Dup ⟨0, by decide⟩),
   opAt 2929 (.Dup ⟨4, by decide⟩),
   opAt 2930 .GT,
   opAt 2931 (.Swap ⟨3, by decide⟩),
   opAt 2932 .POP,
   opAt 2933 (.Dup ⟨2, by decide⟩),
   opAt 2934 .MSTORE,
   opAt 2935 (.Swap ⟨0, by decide⟩),
   opAt 2936 (.Swap ⟨1, by decide⟩),
   opAt 2937 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2938 (.Swap ⟨0, by decide⟩),
   pushAt 2939 1 31,
   opAt 2940 .NOT,
   opAt 2941 .ADD,
   pushAt 2942 2 8255,
   opAt 2943 (.Dup ⟨1, by decide⟩),
   opAt 2944 .GT,
   pushAt 2945 2 3881,
   opAt 2946 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2968 .JUMPDEST,
   opAt 2969 (.Dup ⟨0, by decide⟩),
   opAt 2970 .MLOAD,
   pushAt 2971 2 8256,
   opAt 2972 (.Dup ⟨2, by decide⟩),
   opAt 2973 .SUB,
   opAt 2974 .MLOAD,
   opAt 2975 (.Dup ⟨1, by decide⟩),
   opAt 2976 (.Dup ⟨1, by decide⟩),
   opAt 2977 .GT,
   opAt 2978 (.Swap ⟨1, by decide⟩),
   opAt 2979 .SUB,
   opAt 2980 (.Dup ⟨3, by decide⟩),
   opAt 2981 (.Dup ⟨1, by decide⟩),
   opAt 2982 .LT,
   opAt 2983 (.Swap ⟨0, by decide⟩),
   opAt 2984 (.Dup ⟨4, by decide⟩),
   opAt 2985 (.Swap ⟨0, by decide⟩),
   opAt 2986 .SUB,
   opAt 2987 (.Dup ⟨3, by decide⟩),
   opAt 2988 .MSTORE,
   opAt 2989 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2990 (.Swap ⟨1, by decide⟩),
   opAt 2991 .POP,
   pushAt 2992 1 31,
   opAt 2993 .NOT,
   opAt 2994 .ADD,
   pushAt 2995 2 8255,
   opAt 2996 (.Dup ⟨1, by decide⟩),
   opAt 2997 .GT,
   pushAt 2998 2 3957,
   opAt 2999 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
