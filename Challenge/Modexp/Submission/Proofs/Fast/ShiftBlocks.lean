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

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..38). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2878 .JUMPDEST,
   opAt 2879 (.Dup ⟨0, by decide⟩),
   opAt 2880 .MLOAD,
   pushAt 2881 0 0,
   opAt 2882 .NOT,
   opAt 2883 (.Dup ⟨6, by decide⟩),
   opAt 2884 (.Dup ⟨2, by decide⟩),
   opAt 2885 .MUL,
   opAt 2886 (.Swap ⟨1, by decide⟩),
   opAt 2887 (.Dup ⟨7, by decide⟩),
   opAt 2888 .MULMOD,
   opAt 2889 (.Dup ⟨1, by decide⟩),
   opAt 2890 (.Dup ⟨1, by decide⟩),
   opAt 2891 .LT,
   opAt 2892 .SUB,
   opAt 2893 (.Dup ⟨5, by decide⟩),
   opAt 2894 (.Dup ⟨2, by decide⟩),
   opAt 2895 .ADD,
   opAt 2896 (.Dup ⟨0, by decide⟩),
   opAt 2897 (.Swap ⟨6, by decide⟩),
   opAt 2898 .GT,
   opAt 2899 .SUB,
   opAt 2900 .SUB,
   opAt 2901 (.Dup ⟨4, by decide⟩),
   opAt 2902 (.Dup ⟨3, by decide⟩),
   opAt 2903 .MLOAD,
   opAt 2904 .ADD,
   opAt 2905 (.Dup ⟨0, by decide⟩),
   opAt 2906 (.Swap ⟨5, by decide⟩),
   opAt 2907 .GT,
   opAt 2908 .ADD,
   opAt 2909 (.Swap ⟨3, by decide⟩),
   opAt 2910 (.Dup ⟨2, by decide⟩),
   opAt 2911 (.Dup ⟨4, by decide⟩),
   opAt 2912 .ADD,
   opAt 2913 (.Swap ⟨2, by decide⟩),
   opAt 2914 .MSTORE,
   opAt 2915 (.Dup ⟨2, by decide⟩),
   opAt 2916 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 39..43). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2917 2 8224,
   opAt 2918 (.Dup ⟨2, by decide⟩),
   opAt 2919 .GT,
   pushAt 2920 2 3805,
   opAt 2921 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2955 .JUMPDEST,
   opAt 2956 (.Dup ⟨0, by decide⟩),
   opAt 2957 .MLOAD,
   opAt 2958 (.Dup ⟨1, by decide⟩),
   pushAt 2959 2 8256,
   opAt 2960 (.Swap ⟨0, by decide⟩),
   opAt 2961 .SUB,
   opAt 2962 .MLOAD,
   opAt 2963 (.Dup ⟨1, by decide⟩),
   opAt 2964 .ADD,
   opAt 2965 (.Dup ⟨0, by decide⟩),
   opAt 2966 (.Dup ⟨2, by decide⟩),
   opAt 2967 .GT,
   opAt 2968 (.Swap ⟨1, by decide⟩),
   opAt 2969 .POP,
   opAt 2970 (.Dup ⟨3, by decide⟩),
   opAt 2971 .ADD,
   opAt 2972 (.Dup ⟨0, by decide⟩),
   opAt 2973 (.Dup ⟨4, by decide⟩),
   opAt 2974 .GT,
   opAt 2975 (.Swap ⟨3, by decide⟩),
   opAt 2976 .POP,
   opAt 2977 (.Dup ⟨2, by decide⟩),
   opAt 2978 .MSTORE,
   opAt 2979 (.Swap ⟨0, by decide⟩),
   opAt 2980 (.Swap ⟨1, by decide⟩),
   opAt 2981 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2982 (.Swap ⟨0, by decide⟩),
   pushAt 2983 1 31,
   opAt 2984 .NOT,
   opAt 2985 .ADD,
   pushAt 2986 2 8255,
   opAt 2987 (.Dup ⟨1, by decide⟩),
   opAt 2988 .GT,
   pushAt 2989 2 3894,
   opAt 2990 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3012 .JUMPDEST,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 .MLOAD,
   pushAt 3015 2 8256,
   opAt 3016 (.Dup ⟨2, by decide⟩),
   opAt 3017 .SUB,
   opAt 3018 .MLOAD,
   opAt 3019 (.Dup ⟨1, by decide⟩),
   opAt 3020 (.Dup ⟨1, by decide⟩),
   opAt 3021 .GT,
   opAt 3022 (.Swap ⟨1, by decide⟩),
   opAt 3023 .SUB,
   opAt 3024 (.Dup ⟨3, by decide⟩),
   opAt 3025 (.Dup ⟨1, by decide⟩),
   opAt 3026 .LT,
   opAt 3027 (.Swap ⟨0, by decide⟩),
   opAt 3028 (.Dup ⟨4, by decide⟩),
   opAt 3029 (.Swap ⟨0, by decide⟩),
   opAt 3030 .SUB,
   opAt 3031 (.Dup ⟨3, by decide⟩),
   opAt 3032 .MSTORE,
   opAt 3033 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3034 (.Swap ⟨1, by decide⟩),
   opAt 3035 .POP,
   pushAt 3036 1 31,
   opAt 3037 .NOT,
   opAt 3038 .ADD,
   pushAt 3039 2 8255,
   opAt 3040 (.Dup ⟨1, by decide⟩),
   opAt 3041 .GT,
   pushAt 3042 2 3970,
   opAt 3043 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
