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
  [opAt 2810 .JUMPDEST,
   opAt 2811 (.Dup ⟨0, by decide⟩),
   opAt 2812 .MLOAD,
   opAt 2813 .NOT,
   opAt 2814 (.Dup ⟨2, by decide⟩),
   opAt 2815 .ADD,
   opAt 2816 (.Dup ⟨2, by decide⟩),
   opAt 2817 (.Dup ⟨1, by decide⟩),
   opAt 2818 .LT,
   opAt 2819 (.Swap ⟨2, by decide⟩),
   opAt 2820 .POP,
   opAt 2821 (.Dup ⟨1, by decide⟩),
   pushAt 2822 2 5120,
   opAt 2823 .ADD,
   opAt 2824 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2825 (.Dup ⟨0, by decide⟩),
   opAt 2826 .ISZERO,
   pushAt 2827 2 3888,
   opAt 2828 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3008 .JUMPDEST,
   opAt 3009 (.Dup ⟨0, by decide⟩),
   opAt 3010 .MLOAD,
   pushAt 3011 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3012 (.Dup ⟨5, by decide⟩),
   opAt 3013 (.Dup ⟨2, by decide⟩),
   opAt 3014 .MUL,
   opAt 3015 (.Swap ⟨1, by decide⟩),
   opAt 3016 (.Dup ⟨6, by decide⟩),
   opAt 3017 .MULMOD,
   opAt 3018 (.Dup ⟨1, by decide⟩),
   opAt 3019 (.Dup ⟨1, by decide⟩),
   opAt 3020 .LT,
   opAt 3021 .SUB,
   opAt 3022 (.Dup ⟨4, by decide⟩),
   opAt 3023 (.Dup ⟨2, by decide⟩),
   opAt 3024 .ADD,
   opAt 3025 (.Dup ⟨0, by decide⟩),
   opAt 3026 (.Swap ⟨5, by decide⟩),
   opAt 3027 .GT,
   opAt 3028 .SUB,
   opAt 3029 .SUB,
   opAt 3030 (.Dup ⟨3, by decide⟩),
   opAt 3031 (.Dup ⟨3, by decide⟩),
   opAt 3032 .MLOAD,
   opAt 3033 .ADD,
   opAt 3034 (.Dup ⟨0, by decide⟩),
   opAt 3035 (.Swap ⟨4, by decide⟩),
   opAt 3036 .GT,
   opAt 3037 .ADD,
   opAt 3038 (.Swap ⟨2, by decide⟩),
   opAt 3039 (.Dup ⟨2, by decide⟩),
   pushAt 3040 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3041 .ADD,
   opAt 3042 (.Swap ⟨2, by decide⟩),
   opAt 3043 .MSTORE,
   pushAt 3044 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3045 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3046 2 8224,
   opAt 3047 (.Dup ⟨2, by decide⟩),
   opAt 3048 .GT,
   pushAt 3049 2 4119,
   opAt 3050 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3083 .JUMPDEST,
   opAt 3084 (.Dup ⟨0, by decide⟩),
   opAt 3085 .MLOAD,
   opAt 3086 (.Dup ⟨1, by decide⟩),
   pushAt 3087 2 8256,
   opAt 3088 (.Swap ⟨0, by decide⟩),
   opAt 3089 .SUB,
   opAt 3090 .MLOAD,
   opAt 3091 (.Dup ⟨1, by decide⟩),
   opAt 3092 .ADD,
   opAt 3093 (.Dup ⟨0, by decide⟩),
   opAt 3094 (.Dup ⟨2, by decide⟩),
   opAt 3095 .GT,
   opAt 3096 (.Swap ⟨1, by decide⟩),
   opAt 3097 .POP,
   opAt 3098 (.Dup ⟨3, by decide⟩),
   opAt 3099 .ADD,
   opAt 3100 (.Dup ⟨0, by decide⟩),
   opAt 3101 (.Dup ⟨4, by decide⟩),
   opAt 3102 .GT,
   opAt 3103 (.Swap ⟨3, by decide⟩),
   opAt 3104 .POP,
   opAt 3105 (.Dup ⟨2, by decide⟩),
   opAt 3106 .MSTORE,
   opAt 3107 (.Swap ⟨0, by decide⟩),
   opAt 3108 (.Swap ⟨1, by decide⟩),
   opAt 3109 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3110 (.Swap ⟨0, by decide⟩),
   pushAt 3111 1 31, opAt 3112 .NOT,
   opAt 3113 .ADD,
   pushAt 3114 2 8255,
   opAt 3115 (.Dup ⟨1, by decide⟩),
   opAt 3116 .GT,
   pushAt 3117 2 4302,
   opAt 3118 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3140 .JUMPDEST,
   opAt 3141 (.Dup ⟨0, by decide⟩),
   opAt 3142 .MLOAD,
   opAt 3143 (.Dup ⟨1, by decide⟩),
   pushAt 3144 2 8256,
   opAt 3145 (.Swap ⟨0, by decide⟩),
   opAt 3146 .SUB,
   opAt 3147 .MLOAD,
   opAt 3148 (.Dup ⟨1, by decide⟩),
   opAt 3149 (.Dup ⟨1, by decide⟩),
   opAt 3150 .GT,
   opAt 3151 (.Swap ⟨1, by decide⟩),
   opAt 3152 .SUB,
   opAt 3153 (.Dup ⟨3, by decide⟩),
   opAt 3154 (.Dup ⟨1, by decide⟩),
   opAt 3155 .LT,
   opAt 3156 (.Swap ⟨0, by decide⟩),
   opAt 3157 (.Dup ⟨4, by decide⟩),
   opAt 3158 (.Swap ⟨0, by decide⟩),
   opAt 3159 .SUB,
   opAt 3160 (.Dup ⟨3, by decide⟩),
   opAt 3161 .MSTORE,
   opAt 3162 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3163 (.Swap ⟨1, by decide⟩),
   opAt 3164 .POP,
   pushAt 3165 1 31, opAt 3166 .NOT,
   opAt 3167 .ADD,
   pushAt 3168 2 8255,
   opAt 3169 (.Dup ⟨1, by decide⟩),
   opAt 3170 .GT,
   pushAt 3171 2 4378,
   opAt 3172 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
