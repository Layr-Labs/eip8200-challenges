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
  [opAt 2801 .JUMPDEST,
   opAt 2802 (.Dup ⟨0, by decide⟩),
   opAt 2803 .MLOAD,
   opAt 2804 .NOT,
   opAt 2805 (.Dup ⟨2, by decide⟩),
   opAt 2806 .ADD,
   opAt 2807 (.Dup ⟨2, by decide⟩),
   opAt 2808 (.Dup ⟨1, by decide⟩),
   opAt 2809 .LT,
   opAt 2810 (.Swap ⟨2, by decide⟩),
   opAt 2811 .POP,
   opAt 2812 (.Dup ⟨1, by decide⟩),
   pushAt 2813 2 5120,
   opAt 2814 .ADD,
   opAt 2815 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2816 (.Dup ⟨0, by decide⟩),
   opAt 2817 .ISZERO,
   pushAt 2818 2 3867,
   opAt 2819 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2992 .JUMPDEST,
   opAt 2993 (.Dup ⟨0, by decide⟩),
   opAt 2994 .MLOAD,
   pushAt 2995 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2996 (.Dup ⟨5, by decide⟩),
   opAt 2997 (.Dup ⟨2, by decide⟩),
   opAt 2998 .MUL,
   opAt 2999 (.Swap ⟨1, by decide⟩),
   opAt 3000 (.Dup ⟨6, by decide⟩),
   opAt 3001 .MULMOD,
   opAt 3002 (.Dup ⟨1, by decide⟩),
   opAt 3003 (.Dup ⟨1, by decide⟩),
   opAt 3004 .LT,
   opAt 3005 .SUB,
   opAt 3006 (.Dup ⟨4, by decide⟩),
   opAt 3007 (.Dup ⟨2, by decide⟩),
   opAt 3008 .ADD,
   opAt 3009 (.Dup ⟨0, by decide⟩),
   opAt 3010 (.Swap ⟨5, by decide⟩),
   opAt 3011 .GT,
   opAt 3012 .SUB,
   opAt 3013 .SUB,
   opAt 3014 (.Dup ⟨3, by decide⟩),
   opAt 3015 (.Dup ⟨3, by decide⟩),
   opAt 3016 .MLOAD,
   opAt 3017 .ADD,
   opAt 3018 (.Dup ⟨0, by decide⟩),
   opAt 3019 (.Swap ⟨4, by decide⟩),
   opAt 3020 .GT,
   opAt 3021 .ADD,
   opAt 3022 (.Swap ⟨2, by decide⟩),
   opAt 3023 (.Dup ⟨2, by decide⟩),
   pushAt 3024 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3025 .ADD,
   opAt 3026 (.Swap ⟨2, by decide⟩),
   opAt 3027 .MSTORE,
   pushAt 3028 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3029 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3030 2 8224,
   opAt 3031 (.Dup ⟨2, by decide⟩),
   opAt 3032 .GT,
   pushAt 3033 2 4090,
   opAt 3034 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3067 .JUMPDEST,
   opAt 3068 (.Dup ⟨0, by decide⟩),
   opAt 3069 .MLOAD,
   opAt 3070 (.Dup ⟨1, by decide⟩),
   pushAt 3071 2 8256,
   opAt 3072 (.Swap ⟨0, by decide⟩),
   opAt 3073 .SUB,
   opAt 3074 .MLOAD,
   opAt 3075 (.Dup ⟨1, by decide⟩),
   opAt 3076 .ADD,
   opAt 3077 (.Dup ⟨0, by decide⟩),
   opAt 3078 (.Dup ⟨2, by decide⟩),
   opAt 3079 .GT,
   opAt 3080 (.Swap ⟨1, by decide⟩),
   opAt 3081 .POP,
   opAt 3082 (.Dup ⟨3, by decide⟩),
   opAt 3083 .ADD,
   opAt 3084 (.Dup ⟨0, by decide⟩),
   opAt 3085 (.Dup ⟨4, by decide⟩),
   opAt 3086 .GT,
   opAt 3087 (.Swap ⟨3, by decide⟩),
   opAt 3088 .POP,
   opAt 3089 (.Dup ⟨2, by decide⟩),
   opAt 3090 .MSTORE,
   opAt 3091 (.Swap ⟨0, by decide⟩),
   opAt 3092 (.Swap ⟨1, by decide⟩),
   opAt 3093 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3094 (.Swap ⟨0, by decide⟩),
   pushAt 3095 1 31, opAt 3096 .NOT,
   opAt 3097 .ADD,
   pushAt 3098 2 8255,
   opAt 3099 (.Dup ⟨1, by decide⟩),
   opAt 3100 .GT,
   pushAt 3101 2 4273,
   opAt 3102 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3124 .JUMPDEST,
   opAt 3125 (.Dup ⟨0, by decide⟩),
   opAt 3126 .MLOAD,
   pushAt 3127 2 8256,
   opAt 3128 (.Dup ⟨2, by decide⟩),
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
   pushAt 3154 2 4349,
   opAt 3155 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
