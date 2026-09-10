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
  [opAt 2799 .JUMPDEST,
   opAt 2800 (.Dup ⟨0, by decide⟩),
   opAt 2801 .MLOAD,
   opAt 2802 .NOT,
   opAt 2803 (.Dup ⟨2, by decide⟩),
   opAt 2804 .ADD,
   opAt 2805 (.Dup ⟨2, by decide⟩),
   opAt 2806 (.Dup ⟨1, by decide⟩),
   opAt 2807 .LT,
   opAt 2808 (.Swap ⟨2, by decide⟩),
   opAt 2809 .POP,
   opAt 2810 (.Dup ⟨1, by decide⟩),
   pushAt 2811 2 5120,
   opAt 2812 .ADD,
   opAt 2813 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2814 (.Dup ⟨0, by decide⟩),
   opAt 2815 .ISZERO,
   pushAt 2816 2 3867,
   opAt 2817 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2990 .JUMPDEST,
   opAt 2991 (.Dup ⟨0, by decide⟩),
   opAt 2992 .MLOAD,
   pushAt 2993 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2994 (.Dup ⟨5, by decide⟩),
   opAt 2995 (.Dup ⟨2, by decide⟩),
   opAt 2996 .MUL,
   opAt 2997 (.Swap ⟨1, by decide⟩),
   opAt 2998 (.Dup ⟨6, by decide⟩),
   opAt 2999 .MULMOD,
   opAt 3000 (.Dup ⟨1, by decide⟩),
   opAt 3001 (.Dup ⟨1, by decide⟩),
   opAt 3002 .LT,
   opAt 3003 .SUB,
   opAt 3004 (.Dup ⟨4, by decide⟩),
   opAt 3005 (.Dup ⟨2, by decide⟩),
   opAt 3006 .ADD,
   opAt 3007 (.Dup ⟨0, by decide⟩),
   opAt 3008 (.Swap ⟨5, by decide⟩),
   opAt 3009 .GT,
   opAt 3010 .SUB,
   opAt 3011 .SUB,
   opAt 3012 (.Dup ⟨3, by decide⟩),
   opAt 3013 (.Dup ⟨3, by decide⟩),
   opAt 3014 .MLOAD,
   opAt 3015 .ADD,
   opAt 3016 (.Dup ⟨0, by decide⟩),
   opAt 3017 (.Swap ⟨4, by decide⟩),
   opAt 3018 .GT,
   opAt 3019 .ADD,
   opAt 3020 (.Swap ⟨2, by decide⟩),
   opAt 3021 (.Dup ⟨2, by decide⟩),
   pushAt 3022 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3023 .ADD,
   opAt 3024 (.Swap ⟨2, by decide⟩),
   opAt 3025 .MSTORE,
   pushAt 3026 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3027 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3028 2 8224,
   opAt 3029 (.Dup ⟨2, by decide⟩),
   opAt 3030 .GT,
   pushAt 3031 2 4090,
   opAt 3032 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3065 .JUMPDEST,
   opAt 3066 (.Dup ⟨0, by decide⟩),
   opAt 3067 .MLOAD,
   opAt 3068 (.Dup ⟨1, by decide⟩),
   pushAt 3069 2 8256,
   opAt 3070 (.Swap ⟨0, by decide⟩),
   opAt 3071 .SUB,
   opAt 3072 .MLOAD,
   opAt 3073 (.Dup ⟨1, by decide⟩),
   opAt 3074 .ADD,
   opAt 3075 (.Dup ⟨0, by decide⟩),
   opAt 3076 (.Dup ⟨2, by decide⟩),
   opAt 3077 .GT,
   opAt 3078 (.Swap ⟨1, by decide⟩),
   opAt 3079 .POP,
   opAt 3080 (.Dup ⟨3, by decide⟩),
   opAt 3081 .ADD,
   opAt 3082 (.Dup ⟨0, by decide⟩),
   opAt 3083 (.Dup ⟨4, by decide⟩),
   opAt 3084 .GT,
   opAt 3085 (.Swap ⟨3, by decide⟩),
   opAt 3086 .POP,
   opAt 3087 (.Dup ⟨2, by decide⟩),
   opAt 3088 .MSTORE,
   opAt 3089 (.Swap ⟨0, by decide⟩),
   opAt 3090 (.Swap ⟨1, by decide⟩),
   opAt 3091 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3092 (.Swap ⟨0, by decide⟩),
   pushAt 3093 1 31, opAt 3094 .NOT,
   opAt 3095 .ADD,
   pushAt 3096 2 8255,
   opAt 3097 (.Dup ⟨1, by decide⟩),
   opAt 3098 .GT,
   pushAt 3099 2 4273,
   opAt 3100 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3122 .JUMPDEST,
   opAt 3123 (.Dup ⟨0, by decide⟩),
   opAt 3124 .MLOAD,
   pushAt 3125 2 8256,
   opAt 3126 (.Dup ⟨2, by decide⟩),
   opAt 3127 .SUB,
   opAt 3128 .MLOAD,
   opAt 3129 (.Dup ⟨1, by decide⟩),
   opAt 3130 (.Dup ⟨1, by decide⟩),
   opAt 3131 .GT,
   opAt 3132 (.Swap ⟨1, by decide⟩),
   opAt 3133 .SUB,
   opAt 3134 (.Dup ⟨3, by decide⟩),
   opAt 3135 (.Dup ⟨1, by decide⟩),
   opAt 3136 .LT,
   opAt 3137 (.Swap ⟨0, by decide⟩),
   opAt 3138 (.Dup ⟨4, by decide⟩),
   opAt 3139 (.Swap ⟨0, by decide⟩),
   opAt 3140 .SUB,
   opAt 3141 (.Dup ⟨3, by decide⟩),
   opAt 3142 .MSTORE,
   opAt 3143 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3144 (.Swap ⟨1, by decide⟩),
   opAt 3145 .POP,
   pushAt 3146 1 31, opAt 3147 .NOT,
   opAt 3148 .ADD,
   pushAt 3149 2 8255,
   opAt 3150 (.Dup ⟨1, by decide⟩),
   opAt 3151 .GT,
   pushAt 3152 2 4349,
   opAt 3153 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
