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
  [opAt 2802 .JUMPDEST,
   opAt 2803 (.Dup ⟨0, by decide⟩),
   opAt 2804 .MLOAD,
   opAt 2805 .NOT,
   opAt 2806 (.Dup ⟨2, by decide⟩),
   opAt 2807 .ADD,
   opAt 2808 (.Dup ⟨2, by decide⟩),
   opAt 2809 (.Dup ⟨1, by decide⟩),
   opAt 2810 .LT,
   opAt 2811 (.Swap ⟨2, by decide⟩),
   opAt 2812 .POP,
   opAt 2813 (.Dup ⟨1, by decide⟩),
   pushAt 2814 2 5120,
   opAt 2815 .ADD,
   opAt 2816 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2817 (.Dup ⟨0, by decide⟩),
   opAt 2818 .ISZERO,
   pushAt 2819 2 3903,
   opAt 2820 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2991 .JUMPDEST,
   opAt 2992 (.Dup ⟨0, by decide⟩),
   opAt 2993 .MLOAD,
   pushAt 2994 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2995 (.Dup ⟨5, by decide⟩),
   opAt 2996 (.Dup ⟨2, by decide⟩),
   opAt 2997 .MUL,
   opAt 2998 (.Swap ⟨1, by decide⟩),
   opAt 2999 (.Dup ⟨6, by decide⟩),
   opAt 3000 .MULMOD,
   opAt 3001 (.Dup ⟨1, by decide⟩),
   opAt 3002 (.Dup ⟨1, by decide⟩),
   opAt 3003 .LT,
   opAt 3004 .SUB,
   opAt 3005 (.Dup ⟨4, by decide⟩),
   opAt 3006 (.Dup ⟨2, by decide⟩),
   opAt 3007 .ADD,
   opAt 3008 (.Dup ⟨0, by decide⟩),
   opAt 3009 (.Swap ⟨5, by decide⟩),
   opAt 3010 .GT,
   opAt 3011 .SUB,
   opAt 3012 .SUB,
   opAt 3013 (.Dup ⟨3, by decide⟩),
   opAt 3014 (.Dup ⟨3, by decide⟩),
   opAt 3015 .MLOAD,
   opAt 3016 .ADD,
   opAt 3017 (.Dup ⟨0, by decide⟩),
   opAt 3018 (.Swap ⟨4, by decide⟩),
   opAt 3019 .GT,
   opAt 3020 .ADD,
   opAt 3021 (.Swap ⟨2, by decide⟩),
   opAt 3022 (.Dup ⟨2, by decide⟩),
   pushAt 3023 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3024 .ADD,
   opAt 3025 (.Swap ⟨2, by decide⟩),
   opAt 3026 .MSTORE,
   pushAt 3027 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3028 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3029 2 8224,
   opAt 3030 (.Dup ⟨2, by decide⟩),
   opAt 3031 .GT,
   pushAt 3032 2 4126,
   opAt 3033 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3066 .JUMPDEST,
   opAt 3067 (.Dup ⟨0, by decide⟩),
   opAt 3068 .MLOAD,
   opAt 3069 (.Dup ⟨1, by decide⟩),
   pushAt 3070 2 8256,
   opAt 3071 (.Swap ⟨0, by decide⟩),
   opAt 3072 .SUB,
   opAt 3073 .MLOAD,
   opAt 3074 (.Dup ⟨1, by decide⟩),
   opAt 3075 .ADD,
   opAt 3076 (.Dup ⟨0, by decide⟩),
   opAt 3077 (.Dup ⟨2, by decide⟩),
   opAt 3078 .GT,
   opAt 3079 (.Swap ⟨1, by decide⟩),
   opAt 3080 .POP,
   opAt 3081 (.Dup ⟨3, by decide⟩),
   opAt 3082 .ADD,
   opAt 3083 (.Dup ⟨0, by decide⟩),
   opAt 3084 (.Dup ⟨4, by decide⟩),
   opAt 3085 .GT,
   opAt 3086 (.Swap ⟨3, by decide⟩),
   opAt 3087 .POP,
   opAt 3088 (.Dup ⟨2, by decide⟩),
   opAt 3089 .MSTORE,
   opAt 3090 (.Swap ⟨0, by decide⟩),
   opAt 3091 (.Swap ⟨1, by decide⟩),
   opAt 3092 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3093 (.Swap ⟨0, by decide⟩),
   pushAt 3094 1 31, opAt 3095 .NOT,
   opAt 3096 .ADD,
   pushAt 3097 2 8255,
   opAt 3098 (.Dup ⟨1, by decide⟩),
   opAt 3099 .GT,
   pushAt 3100 2 4309,
   opAt 3101 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3123 .JUMPDEST,
   opAt 3124 (.Dup ⟨0, by decide⟩),
   opAt 3125 .MLOAD,
   opAt 3126 (.Dup ⟨1, by decide⟩),
   pushAt 3127 2 8256,
   opAt 3128 (.Swap ⟨0, by decide⟩),
   opAt 3129 .SUB,
   opAt 3130 .MLOAD,
   opAt 3131 (.Dup ⟨1, by decide⟩),
   opAt 3132 (.Dup ⟨1, by decide⟩),
   opAt 3133 .GT,
   opAt 3134 (.Swap ⟨1, by decide⟩),
   opAt 3135 .SUB,
   opAt 3136 (.Dup ⟨3, by decide⟩),
   opAt 3137 (.Dup ⟨1, by decide⟩),
   opAt 3138 .LT,
   opAt 3139 (.Swap ⟨0, by decide⟩),
   opAt 3140 (.Dup ⟨4, by decide⟩),
   opAt 3141 (.Swap ⟨0, by decide⟩),
   opAt 3142 .SUB,
   opAt 3143 (.Dup ⟨3, by decide⟩),
   opAt 3144 .MSTORE,
   opAt 3145 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3146 (.Swap ⟨1, by decide⟩),
   opAt 3147 .POP,
   pushAt 3148 1 31, opAt 3149 .NOT,
   opAt 3150 .ADD,
   pushAt 3151 2 8255,
   opAt 3152 (.Dup ⟨1, by decide⟩),
   opAt 3153 .GT,
   pushAt 3154 2 4385,
   opAt 3155 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
