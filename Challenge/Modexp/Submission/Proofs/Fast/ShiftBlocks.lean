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
  [opAt 2687 .JUMPDEST,
   opAt 2688 (.Dup ⟨0, by decide⟩),
   opAt 2689 .MLOAD,
   opAt 2690 .NOT,
   opAt 2691 (.Dup ⟨2, by decide⟩),
   opAt 2692 .ADD,
   opAt 2693 (.Dup ⟨2, by decide⟩),
   opAt 2694 (.Dup ⟨1, by decide⟩),
   opAt 2695 .LT,
   opAt 2696 (.Swap ⟨2, by decide⟩),
   opAt 2697 .POP,
   opAt 2698 (.Dup ⟨1, by decide⟩),
   pushAt 2699 2 5120,
   opAt 2700 .ADD,
   opAt 2701 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2702 (.Dup ⟨0, by decide⟩),
   opAt 2703 .ISZERO,
   pushAt 2704 2 3583,
   opAt 2705 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2876 .JUMPDEST,
   opAt 2877 (.Dup ⟨0, by decide⟩),
   opAt 2878 .MLOAD,
   pushAt 2879 0 0,
   opAt 2880 .NOT,
   opAt 2881 (.Dup ⟨5, by decide⟩),
   opAt 2882 (.Dup ⟨2, by decide⟩),
   opAt 2883 .MUL,
   opAt 2884 (.Swap ⟨1, by decide⟩),
   opAt 2885 (.Dup ⟨6, by decide⟩),
   opAt 2886 .MULMOD,
   opAt 2887 (.Dup ⟨1, by decide⟩),
   opAt 2888 (.Dup ⟨1, by decide⟩),
   opAt 2889 .LT,
   opAt 2890 .SUB,
   opAt 2891 (.Dup ⟨4, by decide⟩),
   opAt 2892 (.Dup ⟨2, by decide⟩),
   opAt 2893 .ADD,
   opAt 2894 (.Dup ⟨0, by decide⟩),
   opAt 2895 (.Swap ⟨5, by decide⟩),
   opAt 2896 .GT,
   opAt 2897 .SUB,
   opAt 2898 .SUB,
   opAt 2899 (.Dup ⟨3, by decide⟩),
   opAt 2900 (.Dup ⟨3, by decide⟩),
   opAt 2901 .MLOAD,
   opAt 2902 .ADD,
   opAt 2903 (.Dup ⟨0, by decide⟩),
   opAt 2904 (.Swap ⟨4, by decide⟩),
   opAt 2905 .GT,
   opAt 2906 .ADD,
   opAt 2907 (.Swap ⟨2, by decide⟩),
   opAt 2908 (.Dup ⟨2, by decide⟩),
   pushAt 2909 1 31,
   opAt 2910 .NOT,
   opAt 2911 .ADD,
   opAt 2912 (.Swap ⟨2, by decide⟩),
   opAt 2913 .MSTORE,
   pushAt 2914 1 31,
   opAt 2915 .NOT,
   opAt 2916 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2917 2 8224,
   opAt 2918 (.Dup ⟨2, by decide⟩),
   opAt 2919 .GT,
   pushAt 2920 2 3802,
   opAt 2921 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2954 .JUMPDEST,
   opAt 2955 (.Dup ⟨0, by decide⟩),
   opAt 2956 .MLOAD,
   opAt 2957 (.Dup ⟨1, by decide⟩),
   pushAt 2958 2 8256,
   opAt 2959 (.Swap ⟨0, by decide⟩),
   opAt 2960 .SUB,
   opAt 2961 .MLOAD,
   opAt 2962 (.Dup ⟨1, by decide⟩),
   opAt 2963 .ADD,
   opAt 2964 (.Dup ⟨0, by decide⟩),
   opAt 2965 (.Dup ⟨2, by decide⟩),
   opAt 2966 .GT,
   opAt 2967 (.Swap ⟨1, by decide⟩),
   opAt 2968 .POP,
   opAt 2969 (.Dup ⟨3, by decide⟩),
   opAt 2970 .ADD,
   opAt 2971 (.Dup ⟨0, by decide⟩),
   opAt 2972 (.Dup ⟨4, by decide⟩),
   opAt 2973 .GT,
   opAt 2974 (.Swap ⟨3, by decide⟩),
   opAt 2975 .POP,
   opAt 2976 (.Dup ⟨2, by decide⟩),
   opAt 2977 .MSTORE,
   opAt 2978 (.Swap ⟨0, by decide⟩),
   opAt 2979 (.Swap ⟨1, by decide⟩),
   opAt 2980 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2981 (.Swap ⟨0, by decide⟩),
   pushAt 2982 1 31,
   opAt 2983 .NOT,
   opAt 2984 .ADD,
   pushAt 2985 2 8255,
   opAt 2986 (.Dup ⟨1, by decide⟩),
   opAt 2987 .GT,
   pushAt 2988 2 3894,
   opAt 2989 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3011 .JUMPDEST,
   opAt 3012 (.Dup ⟨0, by decide⟩),
   opAt 3013 .MLOAD,
   pushAt 3014 2 8256,
   opAt 3015 (.Dup ⟨2, by decide⟩),
   opAt 3016 .SUB,
   opAt 3017 .MLOAD,
   opAt 3018 (.Dup ⟨1, by decide⟩),
   opAt 3019 (.Dup ⟨1, by decide⟩),
   opAt 3020 .GT,
   opAt 3021 (.Swap ⟨1, by decide⟩),
   opAt 3022 .SUB,
   opAt 3023 (.Dup ⟨3, by decide⟩),
   opAt 3024 (.Dup ⟨1, by decide⟩),
   opAt 3025 .LT,
   opAt 3026 (.Swap ⟨0, by decide⟩),
   opAt 3027 (.Dup ⟨4, by decide⟩),
   opAt 3028 (.Swap ⟨0, by decide⟩),
   opAt 3029 .SUB,
   opAt 3030 (.Dup ⟨3, by decide⟩),
   opAt 3031 .MSTORE,
   opAt 3032 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3033 (.Swap ⟨1, by decide⟩),
   opAt 3034 .POP,
   pushAt 3035 1 31,
   opAt 3036 .NOT,
   opAt 3037 .ADD,
   pushAt 3038 2 8255,
   opAt 3039 (.Dup ⟨1, by decide⟩),
   opAt 3040 .GT,
   pushAt 3041 2 3970,
   opAt 3042 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
