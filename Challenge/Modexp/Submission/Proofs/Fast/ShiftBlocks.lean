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
  [opAt 2744 .JUMPDEST,
   opAt 2745 (.Dup ⟨0, by decide⟩),
   opAt 2746 .MLOAD,
   opAt 2747 .NOT,
   opAt 2748 (.Dup ⟨2, by decide⟩),
   opAt 2749 .ADD,
   opAt 2750 (.Dup ⟨2, by decide⟩),
   opAt 2751 (.Dup ⟨1, by decide⟩),
   opAt 2752 .LT,
   opAt 2753 (.Swap ⟨2, by decide⟩),
   opAt 2754 .POP,
   opAt 2755 (.Dup ⟨1, by decide⟩),
   pushAt 2756 2 5120,
   opAt 2757 .ADD,
   opAt 2758 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2759 (.Dup ⟨0, by decide⟩),
   opAt 2760 .ISZERO,
   pushAt 2761 2 4735,
   opAt 2762 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2932 .JUMPDEST,
   opAt 2933 (.Dup ⟨0, by decide⟩),
   opAt 2934 .MLOAD,
   pushAt 2935 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2936 (.Dup ⟨5, by decide⟩),
   opAt 2937 (.Dup ⟨2, by decide⟩),
   opAt 2938 .MUL,
   opAt 2939 (.Swap ⟨1, by decide⟩),
   opAt 2940 (.Dup ⟨6, by decide⟩),
   opAt 2941 .MULMOD,
   opAt 2942 (.Dup ⟨1, by decide⟩),
   opAt 2943 (.Dup ⟨1, by decide⟩),
   opAt 2944 .LT,
   opAt 2945 .SUB,
   opAt 2946 (.Dup ⟨4, by decide⟩),
   opAt 2947 (.Dup ⟨2, by decide⟩),
   opAt 2948 .ADD,
   opAt 2949 (.Dup ⟨0, by decide⟩),
   opAt 2950 (.Swap ⟨5, by decide⟩),
   opAt 2951 .GT,
   opAt 2952 .SUB,
   opAt 2953 .SUB,
   opAt 2954 (.Dup ⟨3, by decide⟩),
   opAt 2955 (.Dup ⟨3, by decide⟩),
   opAt 2956 .MLOAD,
   opAt 2957 .ADD,
   opAt 2958 (.Dup ⟨0, by decide⟩),
   opAt 2959 (.Swap ⟨4, by decide⟩),
   opAt 2960 .GT,
   opAt 2961 .ADD,
   opAt 2962 (.Swap ⟨2, by decide⟩),
   opAt 2963 (.Dup ⟨2, by decide⟩),
   pushAt 2964 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2965 .ADD,
   opAt 2966 (.Swap ⟨2, by decide⟩),
   opAt 2967 .MSTORE,
   pushAt 2968 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2969 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2970 2 8224,
   opAt 2971 (.Dup ⟨2, by decide⟩),
   opAt 2972 .GT,
   pushAt 2973 2 4952,
   opAt 2974 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3007 .JUMPDEST,
   opAt 3008 (.Dup ⟨0, by decide⟩),
   opAt 3009 .MLOAD,
   opAt 3010 (.Dup ⟨1, by decide⟩),
   pushAt 3011 2 8256,
   opAt 3012 (.Swap ⟨0, by decide⟩),
   opAt 3013 .SUB,
   opAt 3014 .MLOAD,
   opAt 3015 (.Dup ⟨1, by decide⟩),
   opAt 3016 .ADD,
   opAt 3017 (.Dup ⟨0, by decide⟩),
   opAt 3018 (.Dup ⟨2, by decide⟩),
   opAt 3019 .GT,
   opAt 3020 (.Swap ⟨1, by decide⟩),
   opAt 3021 .POP,
   opAt 3022 (.Dup ⟨3, by decide⟩),
   opAt 3023 .ADD,
   opAt 3024 (.Dup ⟨0, by decide⟩),
   opAt 3025 (.Dup ⟨4, by decide⟩),
   opAt 3026 .GT,
   opAt 3027 (.Swap ⟨3, by decide⟩),
   opAt 3028 .POP,
   opAt 3029 (.Dup ⟨2, by decide⟩),
   opAt 3030 .MSTORE,
   opAt 3031 (.Swap ⟨0, by decide⟩),
   opAt 3032 (.Swap ⟨1, by decide⟩),
   opAt 3033 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3034 (.Swap ⟨0, by decide⟩),
   pushAt 3035 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3036 .ADD,
   pushAt 3037 2 8255,
   opAt 3038 (.Dup ⟨1, by decide⟩),
   opAt 3039 .GT,
   pushAt 3040 2 5135,
   opAt 3041 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3063 .JUMPDEST,
   opAt 3064 (.Dup ⟨0, by decide⟩),
   opAt 3065 .MLOAD,
   opAt 3066 (.Dup ⟨1, by decide⟩),
   pushAt 3067 2 8256,
   opAt 3068 (.Swap ⟨0, by decide⟩),
   opAt 3069 .SUB,
   opAt 3070 .MLOAD,
   opAt 3071 (.Dup ⟨1, by decide⟩),
   opAt 3072 (.Dup ⟨1, by decide⟩),
   opAt 3073 .GT,
   opAt 3074 (.Swap ⟨1, by decide⟩),
   opAt 3075 .SUB,
   opAt 3076 (.Dup ⟨3, by decide⟩),
   opAt 3077 (.Dup ⟨1, by decide⟩),
   opAt 3078 .LT,
   opAt 3079 (.Swap ⟨0, by decide⟩),
   opAt 3080 (.Dup ⟨4, by decide⟩),
   opAt 3081 (.Swap ⟨0, by decide⟩),
   opAt 3082 .SUB,
   opAt 3083 (.Dup ⟨3, by decide⟩),
   opAt 3084 .MSTORE,
   opAt 3085 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3086 (.Swap ⟨1, by decide⟩),
   opAt 3087 .POP,
   pushAt 3088 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3089 .ADD,
   pushAt 3090 2 8255,
   opAt 3091 (.Dup ⟨1, by decide⟩),
   opAt 3092 .GT,
   pushAt 3093 2 5241,
   opAt 3094 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
