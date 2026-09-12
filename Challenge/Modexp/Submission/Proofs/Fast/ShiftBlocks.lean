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
  [opAt 2644 .JUMPDEST,
   opAt 2645 (.Dup ⟨0, by decide⟩),
   opAt 2646 .MLOAD,
   opAt 2647 .NOT,
   opAt 2648 (.Dup ⟨2, by decide⟩),
   opAt 2649 .ADD,
   opAt 2650 (.Dup ⟨2, by decide⟩),
   opAt 2651 (.Dup ⟨1, by decide⟩),
   opAt 2652 .LT,
   opAt 2653 (.Swap ⟨2, by decide⟩),
   opAt 2654 .POP,
   opAt 2655 (.Dup ⟨1, by decide⟩),
   pushAt 2656 2 1280,
   opAt 2657 .ADD,
   opAt 2658 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2659 (.Dup ⟨0, by decide⟩),
   opAt 2660 .ISZERO,
   pushAt 2661 2 3536,
   opAt 2662 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2835 .JUMPDEST,
   opAt 2836 (.Dup ⟨0, by decide⟩),
   opAt 2837 .MLOAD,
   pushAt 2838 0 0,
   opAt 2839 .NOT,
   opAt 2840 (.Dup ⟨5, by decide⟩),
   opAt 2841 (.Dup ⟨2, by decide⟩),
   opAt 2842 .MUL,
   opAt 2843 (.Swap ⟨1, by decide⟩),
   opAt 2844 (.Dup ⟨6, by decide⟩),
   opAt 2845 .MULMOD,
   opAt 2846 (.Dup ⟨1, by decide⟩),
   opAt 2847 (.Dup ⟨1, by decide⟩),
   opAt 2848 .LT,
   opAt 2849 .SUB,
   opAt 2850 (.Dup ⟨4, by decide⟩),
   opAt 2851 (.Dup ⟨2, by decide⟩),
   opAt 2852 .ADD,
   opAt 2853 (.Dup ⟨0, by decide⟩),
   opAt 2854 (.Swap ⟨5, by decide⟩),
   opAt 2855 .GT,
   opAt 2856 .SUB,
   opAt 2857 .SUB,
   opAt 2858 (.Dup ⟨3, by decide⟩),
   opAt 2859 (.Dup ⟨3, by decide⟩),
   opAt 2860 .MLOAD,
   opAt 2861 .ADD,
   opAt 2862 (.Dup ⟨0, by decide⟩),
   opAt 2863 (.Swap ⟨4, by decide⟩),
   opAt 2864 .GT,
   opAt 2865 .ADD,
   opAt 2866 (.Swap ⟨2, by decide⟩),
   opAt 2867 (.Dup ⟨2, by decide⟩),
   pushAt 2868 1 31,
   opAt 2869 .NOT,
   opAt 2870 .ADD,
   opAt 2871 (.Swap ⟨2, by decide⟩),
   opAt 2872 .MSTORE,
   pushAt 2873 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2874 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2875 2 4128,
   opAt 2876 (.Dup ⟨2, by decide⟩),
   opAt 2877 .GT,
   pushAt 2878 2 3759,
   opAt 2879 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2912 .JUMPDEST,
   opAt 2913 (.Dup ⟨0, by decide⟩),
   opAt 2914 .MLOAD,
   opAt 2915 (.Dup ⟨1, by decide⟩),
   pushAt 2916 2 4160,
   opAt 2917 (.Swap ⟨0, by decide⟩),
   opAt 2918 .SUB,
   opAt 2919 .MLOAD,
   opAt 2920 (.Dup ⟨1, by decide⟩),
   opAt 2921 .ADD,
   opAt 2922 (.Dup ⟨0, by decide⟩),
   opAt 2923 (.Dup ⟨2, by decide⟩),
   opAt 2924 .GT,
   opAt 2925 (.Swap ⟨1, by decide⟩),
   opAt 2926 .POP,
   opAt 2927 (.Dup ⟨3, by decide⟩),
   opAt 2928 .ADD,
   opAt 2929 (.Dup ⟨0, by decide⟩),
   opAt 2930 (.Dup ⟨4, by decide⟩),
   opAt 2931 .GT,
   opAt 2932 (.Swap ⟨3, by decide⟩),
   opAt 2933 .POP,
   opAt 2934 (.Dup ⟨2, by decide⟩),
   opAt 2935 .MSTORE,
   opAt 2936 (.Swap ⟨0, by decide⟩),
   opAt 2937 (.Swap ⟨1, by decide⟩),
   opAt 2938 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2939 (.Swap ⟨0, by decide⟩),
   pushAt 2940 1 31,
   opAt 2941 .NOT,
   opAt 2942 .ADD,
   pushAt 2943 2 4159,
   opAt 2944 (.Dup ⟨1, by decide⟩),
   opAt 2945 .GT,
   pushAt 2946 2 3881,
   opAt 2947 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2969 .JUMPDEST,
   opAt 2970 (.Dup ⟨0, by decide⟩),
   opAt 2971 .MLOAD,
   pushAt 2972 2 4160,
   opAt 2973 (.Dup ⟨2, by decide⟩),
   opAt 2974 .SUB,
   opAt 2975 .MLOAD,
   opAt 2976 (.Dup ⟨1, by decide⟩),
   opAt 2977 (.Dup ⟨1, by decide⟩),
   opAt 2978 .GT,
   opAt 2979 (.Swap ⟨1, by decide⟩),
   opAt 2980 .SUB,
   opAt 2981 (.Dup ⟨3, by decide⟩),
   opAt 2982 (.Dup ⟨1, by decide⟩),
   opAt 2983 .LT,
   opAt 2984 (.Swap ⟨0, by decide⟩),
   opAt 2985 (.Dup ⟨4, by decide⟩),
   opAt 2986 (.Swap ⟨0, by decide⟩),
   opAt 2987 .SUB,
   opAt 2988 (.Dup ⟨3, by decide⟩),
   opAt 2989 .MSTORE,
   opAt 2990 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2991 (.Swap ⟨1, by decide⟩),
   opAt 2992 .POP,
   pushAt 2993 1 31,
   opAt 2994 .NOT,
   opAt 2995 .ADD,
   pushAt 2996 2 4159,
   opAt 2997 (.Dup ⟨1, by decide⟩),
   opAt 2998 .GT,
   pushAt 2999 2 3957,
   opAt 3000 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
