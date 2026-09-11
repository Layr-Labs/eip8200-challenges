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
  [opAt 2878 .JUMPDEST,
   opAt 2879 (.Dup ⟨0, by decide⟩),
   opAt 2880 .MLOAD,
   pushAt 2881 0 0,
   opAt 2882 .NOT,
   opAt 2883 (.Dup ⟨5, by decide⟩),
   opAt 2884 (.Dup ⟨2, by decide⟩),
   opAt 2885 .MUL,
   opAt 2886 (.Swap ⟨1, by decide⟩),
   opAt 2887 (.Dup ⟨6, by decide⟩),
   opAt 2888 .MULMOD,
   opAt 2889 (.Dup ⟨1, by decide⟩),
   opAt 2890 (.Dup ⟨1, by decide⟩),
   opAt 2891 .LT,
   opAt 2892 .SUB,
   opAt 2893 (.Dup ⟨4, by decide⟩),
   opAt 2894 (.Dup ⟨2, by decide⟩),
   opAt 2895 .ADD,
   opAt 2896 (.Dup ⟨0, by decide⟩),
   opAt 2897 (.Swap ⟨5, by decide⟩),
   opAt 2898 .GT,
   opAt 2899 .SUB,
   opAt 2900 .SUB,
   opAt 2901 (.Dup ⟨3, by decide⟩),
   opAt 2902 (.Dup ⟨3, by decide⟩),
   opAt 2903 .MLOAD,
   opAt 2904 .ADD,
   opAt 2905 (.Dup ⟨0, by decide⟩),
   opAt 2906 (.Swap ⟨4, by decide⟩),
   opAt 2907 .GT,
   opAt 2908 .ADD,
   opAt 2909 (.Swap ⟨2, by decide⟩),
   opAt 2910 (.Dup ⟨2, by decide⟩),
   pushAt 2911 1 31,
   opAt 2912 .NOT,
   opAt 2913 .ADD,
   opAt 2914 (.Swap ⟨2, by decide⟩),
   opAt 2915 .MSTORE,
   pushAt 2916 1 31,
   opAt 2917 .NOT,
   opAt 2918 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2919 2 8224,
   opAt 2920 (.Dup ⟨2, by decide⟩),
   opAt 2921 .GT,
   pushAt 2922 2 3806,
   opAt 2923 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2956 .JUMPDEST,
   opAt 2957 (.Dup ⟨0, by decide⟩),
   opAt 2958 .MLOAD,
   opAt 2959 (.Dup ⟨1, by decide⟩),
   pushAt 2960 2 8256,
   opAt 2961 (.Swap ⟨0, by decide⟩),
   opAt 2962 .SUB,
   opAt 2963 .MLOAD,
   opAt 2964 (.Dup ⟨1, by decide⟩),
   opAt 2965 .ADD,
   opAt 2966 (.Dup ⟨0, by decide⟩),
   opAt 2967 (.Dup ⟨2, by decide⟩),
   opAt 2968 .GT,
   opAt 2969 (.Swap ⟨1, by decide⟩),
   opAt 2970 .POP,
   opAt 2971 (.Dup ⟨3, by decide⟩),
   opAt 2972 .ADD,
   opAt 2973 (.Dup ⟨0, by decide⟩),
   opAt 2974 (.Dup ⟨4, by decide⟩),
   opAt 2975 .GT,
   opAt 2976 (.Swap ⟨3, by decide⟩),
   opAt 2977 .POP,
   opAt 2978 (.Dup ⟨2, by decide⟩),
   opAt 2979 .MSTORE,
   opAt 2980 (.Swap ⟨0, by decide⟩),
   opAt 2981 (.Swap ⟨1, by decide⟩),
   opAt 2982 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2983 (.Swap ⟨0, by decide⟩),
   pushAt 2984 1 31,
   opAt 2985 .NOT,
   opAt 2986 .ADD,
   pushAt 2987 2 8255,
   opAt 2988 (.Dup ⟨1, by decide⟩),
   opAt 2989 .GT,
   pushAt 2990 2 3898,
   opAt 2991 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3013 .JUMPDEST,
   opAt 3014 (.Dup ⟨0, by decide⟩),
   opAt 3015 .MLOAD,
   pushAt 3016 2 8256,
   opAt 3017 (.Dup ⟨2, by decide⟩),
   opAt 3018 .SUB,
   opAt 3019 .MLOAD,
   opAt 3020 (.Dup ⟨1, by decide⟩),
   opAt 3021 (.Dup ⟨1, by decide⟩),
   opAt 3022 .GT,
   opAt 3023 (.Swap ⟨1, by decide⟩),
   opAt 3024 .SUB,
   opAt 3025 (.Dup ⟨3, by decide⟩),
   opAt 3026 (.Dup ⟨1, by decide⟩),
   opAt 3027 .LT,
   opAt 3028 (.Swap ⟨0, by decide⟩),
   opAt 3029 (.Dup ⟨4, by decide⟩),
   opAt 3030 (.Swap ⟨0, by decide⟩),
   opAt 3031 .SUB,
   opAt 3032 (.Dup ⟨3, by decide⟩),
   opAt 3033 .MSTORE,
   opAt 3034 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3035 (.Swap ⟨1, by decide⟩),
   opAt 3036 .POP,
   pushAt 3037 1 31,
   opAt 3038 .NOT,
   opAt 3039 .ADD,
   pushAt 3040 2 8255,
   opAt 3041 (.Dup ⟨1, by decide⟩),
   opAt 3042 .GT,
   pushAt 3043 2 3974,
   opAt 3044 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
