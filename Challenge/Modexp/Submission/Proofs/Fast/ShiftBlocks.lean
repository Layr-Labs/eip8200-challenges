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
   pushAt 2827 2 3903,
   opAt 2828 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2998 .JUMPDEST,
   opAt 2999 (.Dup ⟨0, by decide⟩),
   opAt 3000 .MLOAD,
   pushAt 3001 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3002 (.Dup ⟨5, by decide⟩),
   opAt 3003 (.Dup ⟨2, by decide⟩),
   opAt 3004 .MUL,
   opAt 3005 (.Swap ⟨1, by decide⟩),
   opAt 3006 (.Dup ⟨6, by decide⟩),
   opAt 3007 .MULMOD,
   opAt 3008 (.Dup ⟨1, by decide⟩),
   opAt 3009 (.Dup ⟨1, by decide⟩),
   opAt 3010 .LT,
   opAt 3011 .SUB,
   opAt 3012 (.Dup ⟨4, by decide⟩),
   opAt 3013 (.Dup ⟨2, by decide⟩),
   opAt 3014 .ADD,
   opAt 3015 (.Dup ⟨0, by decide⟩),
   opAt 3016 (.Swap ⟨5, by decide⟩),
   opAt 3017 .GT,
   opAt 3018 .SUB,
   opAt 3019 .SUB,
   opAt 3020 (.Dup ⟨3, by decide⟩),
   opAt 3021 (.Dup ⟨3, by decide⟩),
   opAt 3022 .MLOAD,
   opAt 3023 .ADD,
   opAt 3024 (.Dup ⟨0, by decide⟩),
   opAt 3025 (.Swap ⟨4, by decide⟩),
   opAt 3026 .GT,
   opAt 3027 .ADD,
   opAt 3028 (.Swap ⟨2, by decide⟩),
   opAt 3029 (.Dup ⟨2, by decide⟩),
   pushAt 3030 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3031 .ADD,
   opAt 3032 (.Swap ⟨2, by decide⟩),
   opAt 3033 .MSTORE,
   pushAt 3034 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3035 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3036 2 8224,
   opAt 3037 (.Dup ⟨2, by decide⟩),
   opAt 3038 .GT,
   pushAt 3039 2 4119,
   opAt 3040 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3073 .JUMPDEST,
   opAt 3074 (.Dup ⟨0, by decide⟩),
   opAt 3075 .MLOAD,
   opAt 3076 (.Dup ⟨1, by decide⟩),
   pushAt 3077 2 8256,
   opAt 3078 (.Swap ⟨0, by decide⟩),
   opAt 3079 .SUB,
   opAt 3080 .MLOAD,
   opAt 3081 (.Dup ⟨1, by decide⟩),
   opAt 3082 .ADD,
   opAt 3083 (.Dup ⟨0, by decide⟩),
   opAt 3084 (.Dup ⟨2, by decide⟩),
   opAt 3085 .GT,
   opAt 3086 (.Swap ⟨1, by decide⟩),
   opAt 3087 .POP,
   opAt 3088 (.Dup ⟨3, by decide⟩),
   opAt 3089 .ADD,
   opAt 3090 (.Dup ⟨0, by decide⟩),
   opAt 3091 (.Dup ⟨4, by decide⟩),
   opAt 3092 .GT,
   opAt 3093 (.Swap ⟨3, by decide⟩),
   opAt 3094 .POP,
   opAt 3095 (.Dup ⟨2, by decide⟩),
   opAt 3096 .MSTORE,
   opAt 3097 (.Swap ⟨0, by decide⟩),
   opAt 3098 (.Swap ⟨1, by decide⟩),
   opAt 3099 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3100 (.Swap ⟨0, by decide⟩),
   pushAt 3101 1 31, opAt 3102 .NOT,
   opAt 3103 .ADD,
   pushAt 3104 2 8255,
   opAt 3105 (.Dup ⟨1, by decide⟩),
   opAt 3106 .GT,
   pushAt 3107 2 4302,
   opAt 3108 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3130 .JUMPDEST,
   opAt 3131 (.Dup ⟨0, by decide⟩),
   opAt 3132 .MLOAD,
   pushAt 3133 2 8256,
   opAt 3134 (.Dup ⟨2, by decide⟩),
   opAt 3135 .JUMPDEST,
   opAt 3136 .SUB,
   opAt 3137 .MLOAD,
   opAt 3138 (.Dup ⟨1, by decide⟩),
   opAt 3139 (.Dup ⟨1, by decide⟩),
   opAt 3140 .GT,
   opAt 3141 (.Swap ⟨1, by decide⟩),
   opAt 3142 .SUB,
   opAt 3143 (.Dup ⟨3, by decide⟩),
   opAt 3144 (.Dup ⟨1, by decide⟩),
   opAt 3145 .LT,
   opAt 3146 (.Swap ⟨0, by decide⟩),
   opAt 3147 (.Dup ⟨4, by decide⟩),
   opAt 3148 (.Swap ⟨0, by decide⟩),
   opAt 3149 .SUB,
   opAt 3150 (.Dup ⟨3, by decide⟩),
   opAt 3151 .MSTORE,
   opAt 3152 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3153 (.Swap ⟨1, by decide⟩),
   opAt 3154 .POP,
   pushAt 3155 1 31, opAt 3156 .NOT,
   opAt 3157 .ADD,
   pushAt 3158 2 8255,
   opAt 3159 (.Dup ⟨1, by decide⟩),
   opAt 3160 .GT,
   pushAt 3161 2 4378,
   opAt 3162 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
