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
  [opAt 2736 .JUMPDEST,
   opAt 2737 (.Dup ⟨0, by decide⟩),
   opAt 2738 .MLOAD,
   opAt 2739 .NOT,
   opAt 2740 (.Dup ⟨2, by decide⟩),
   opAt 2741 .ADD,
   opAt 2742 (.Dup ⟨2, by decide⟩),
   opAt 2743 (.Dup ⟨1, by decide⟩),
   opAt 2744 .LT,
   opAt 2745 (.Swap ⟨2, by decide⟩),
   opAt 2746 .POP,
   opAt 2747 (.Dup ⟨1, by decide⟩),
   pushAt 2748 2 5120,
   opAt 2749 .ADD,
   opAt 2750 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2751 (.Dup ⟨0, by decide⟩),
   opAt 2752 .ISZERO,
   pushAt 2753 2 3671,
   opAt 2754 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2925 .JUMPDEST,
   opAt 2926 (.Dup ⟨0, by decide⟩),
   opAt 2927 .MLOAD,
   pushAt 2928 0 0,
   opAt 2929 .NOT,
   opAt 2930 (.Dup ⟨5, by decide⟩),
   opAt 2931 (.Dup ⟨2, by decide⟩),
   opAt 2932 .MUL,
   opAt 2933 (.Swap ⟨1, by decide⟩),
   opAt 2934 (.Dup ⟨6, by decide⟩),
   opAt 2935 .MULMOD,
   opAt 2936 (.Dup ⟨1, by decide⟩),
   opAt 2937 (.Dup ⟨1, by decide⟩),
   opAt 2938 .LT,
   opAt 2939 .SUB,
   opAt 2940 (.Dup ⟨4, by decide⟩),
   opAt 2941 (.Dup ⟨2, by decide⟩),
   opAt 2942 .ADD,
   opAt 2943 (.Dup ⟨0, by decide⟩),
   opAt 2944 (.Swap ⟨5, by decide⟩),
   opAt 2945 .GT,
   opAt 2946 .SUB,
   opAt 2947 .SUB,
   opAt 2948 (.Dup ⟨3, by decide⟩),
   opAt 2949 (.Dup ⟨3, by decide⟩),
   opAt 2950 .MLOAD,
   opAt 2951 .ADD,
   opAt 2952 (.Dup ⟨0, by decide⟩),
   opAt 2953 (.Swap ⟨4, by decide⟩),
   opAt 2954 .GT,
   opAt 2955 .ADD,
   opAt 2956 (.Swap ⟨2, by decide⟩),
   opAt 2957 (.Dup ⟨2, by decide⟩),
   pushAt 2958 1 31,
   opAt 2959 .NOT,
   opAt 2960 .ADD,
   opAt 2961 (.Swap ⟨2, by decide⟩),
   opAt 2962 .MSTORE,
   pushAt 2963 1 31,
   opAt 2964 .NOT,
   opAt 2965 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2966 2 8224,
   opAt 2967 (.Dup ⟨2, by decide⟩),
   opAt 2968 .GT,
   pushAt 2969 2 3890,
   opAt 2970 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3003 .JUMPDEST,
   opAt 3004 (.Dup ⟨0, by decide⟩),
   opAt 3005 .MLOAD,
   opAt 3006 (.Dup ⟨1, by decide⟩),
   pushAt 3007 2 8256,
   opAt 3008 (.Swap ⟨0, by decide⟩),
   opAt 3009 .SUB,
   opAt 3010 .MLOAD,
   opAt 3011 (.Dup ⟨1, by decide⟩),
   opAt 3012 .ADD,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 (.Dup ⟨2, by decide⟩),
   opAt 3015 .GT,
   opAt 3016 (.Swap ⟨1, by decide⟩),
   opAt 3017 .POP,
   opAt 3018 (.Dup ⟨3, by decide⟩),
   opAt 3019 .ADD,
   opAt 3020 (.Dup ⟨0, by decide⟩),
   opAt 3021 (.Dup ⟨4, by decide⟩),
   opAt 3022 .GT,
   opAt 3023 (.Swap ⟨3, by decide⟩),
   opAt 3024 .POP,
   opAt 3025 (.Dup ⟨2, by decide⟩),
   opAt 3026 .MSTORE,
   opAt 3027 (.Swap ⟨0, by decide⟩),
   opAt 3028 (.Swap ⟨1, by decide⟩),
   opAt 3029 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3030 (.Swap ⟨0, by decide⟩),
   pushAt 3031 1 31,
   opAt 3032 .NOT,
   opAt 3033 .ADD,
   pushAt 3034 2 8255,
   opAt 3035 (.Dup ⟨1, by decide⟩),
   opAt 3036 .GT,
   pushAt 3037 2 3982,
   opAt 3038 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3060 .JUMPDEST,
   opAt 3061 (.Dup ⟨0, by decide⟩),
   opAt 3062 .MLOAD,
   pushAt 3063 2 8256,
   opAt 3064 (.Dup ⟨2, by decide⟩),
   opAt 3065 .SUB,
   opAt 3066 .MLOAD,
   opAt 3067 (.Dup ⟨1, by decide⟩),
   opAt 3068 (.Dup ⟨1, by decide⟩),
   opAt 3069 .GT,
   opAt 3070 (.Swap ⟨1, by decide⟩),
   opAt 3071 .SUB,
   opAt 3072 (.Dup ⟨3, by decide⟩),
   opAt 3073 (.Dup ⟨1, by decide⟩),
   opAt 3074 .LT,
   opAt 3075 (.Swap ⟨0, by decide⟩),
   opAt 3076 (.Dup ⟨4, by decide⟩),
   opAt 3077 (.Swap ⟨0, by decide⟩),
   opAt 3078 .SUB,
   opAt 3079 (.Dup ⟨3, by decide⟩),
   opAt 3080 .MSTORE,
   opAt 3081 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3082 (.Swap ⟨1, by decide⟩),
   opAt 3083 .POP,
   pushAt 3084 1 31,
   opAt 3085 .NOT,
   opAt 3086 .ADD,
   pushAt 3087 2 8255,
   opAt 3088 (.Dup ⟨1, by decide⟩),
   opAt 3089 .GT,
   pushAt 3090 2 4058,
   opAt 3091 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
