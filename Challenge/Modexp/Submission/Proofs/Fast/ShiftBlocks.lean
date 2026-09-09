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
  [opAt 2988 .JUMPDEST,
   opAt 2989 (.Dup ⟨0, by decide⟩),
   opAt 2990 .MLOAD,
   pushAt 2991 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2992 (.Dup ⟨5, by decide⟩),
   opAt 2993 (.Dup ⟨2, by decide⟩),
   opAt 2994 .MUL,
   opAt 2995 (.Swap ⟨1, by decide⟩),
   opAt 2996 (.Dup ⟨6, by decide⟩),
   opAt 2997 .MULMOD,
   opAt 2998 (.Dup ⟨1, by decide⟩),
   opAt 2999 (.Dup ⟨1, by decide⟩),
   opAt 3000 .LT,
   opAt 3001 .SUB,
   opAt 3002 (.Dup ⟨4, by decide⟩),
   opAt 3003 (.Dup ⟨2, by decide⟩),
   opAt 3004 .ADD,
   opAt 3005 (.Dup ⟨0, by decide⟩),
   opAt 3006 (.Swap ⟨5, by decide⟩),
   opAt 3007 .GT,
   opAt 3008 .SUB,
   opAt 3009 .SUB,
   opAt 3010 (.Dup ⟨3, by decide⟩),
   opAt 3011 (.Dup ⟨3, by decide⟩),
   opAt 3012 .MLOAD,
   opAt 3013 .ADD,
   opAt 3014 (.Dup ⟨0, by decide⟩),
   opAt 3015 (.Swap ⟨4, by decide⟩),
   opAt 3016 .GT,
   opAt 3017 .ADD,
   opAt 3018 (.Swap ⟨2, by decide⟩),
   opAt 3019 (.Dup ⟨2, by decide⟩),
   pushAt 3020 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3021 .ADD,
   opAt 3022 (.Swap ⟨2, by decide⟩),
   opAt 3023 .MSTORE,
   pushAt 3024 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3025 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3026 2 8224,
   opAt 3027 (.Dup ⟨2, by decide⟩),
   opAt 3028 .GT,
   pushAt 3029 2 4086,
   opAt 3030 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
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
   opAt 3072 .ADD,
   opAt 3073 (.Dup ⟨0, by decide⟩),
   opAt 3074 (.Dup ⟨2, by decide⟩),
   opAt 3075 .GT,
   opAt 3076 (.Swap ⟨1, by decide⟩),
   opAt 3077 .POP,
   opAt 3078 (.Dup ⟨3, by decide⟩),
   opAt 3079 .ADD,
   opAt 3080 (.Dup ⟨0, by decide⟩),
   opAt 3081 (.Dup ⟨4, by decide⟩),
   opAt 3082 .GT,
   opAt 3083 (.Swap ⟨3, by decide⟩),
   opAt 3084 .POP,
   opAt 3085 (.Dup ⟨2, by decide⟩),
   opAt 3086 .MSTORE,
   opAt 3087 (.Swap ⟨0, by decide⟩),
   opAt 3088 (.Swap ⟨1, by decide⟩),
   opAt 3089 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3090 (.Swap ⟨0, by decide⟩),
   pushAt 3091 1 31, opAt 3092 .NOT,
   opAt 3093 .ADD,
   pushAt 3094 2 8255,
   opAt 3095 (.Dup ⟨1, by decide⟩),
   opAt 3096 .GT,
   pushAt 3097 2 4269,
   opAt 3098 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3120 .JUMPDEST,
   opAt 3121 (.Dup ⟨0, by decide⟩),
   opAt 3122 .MLOAD,
   pushAt 3123 2 8256,
   opAt 3124 (.Dup ⟨2, by decide⟩),
   opAt 3125 .SUB,
   opAt 3126 .MLOAD,
   opAt 3127 (.Dup ⟨1, by decide⟩),
   opAt 3128 (.Dup ⟨1, by decide⟩),
   opAt 3129 .GT,
   opAt 3130 (.Swap ⟨1, by decide⟩),
   opAt 3131 .SUB,
   opAt 3132 (.Dup ⟨3, by decide⟩),
   opAt 3133 (.Dup ⟨1, by decide⟩),
   opAt 3134 .LT,
   opAt 3135 (.Swap ⟨0, by decide⟩),
   opAt 3136 (.Dup ⟨4, by decide⟩),
   opAt 3137 (.Swap ⟨0, by decide⟩),
   opAt 3138 .SUB,
   opAt 3139 (.Dup ⟨3, by decide⟩),
   opAt 3140 .MSTORE,
   opAt 3141 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3142 (.Swap ⟨1, by decide⟩),
   opAt 3143 .POP,
   pushAt 3144 1 31, opAt 3145 .NOT,
   opAt 3146 .ADD,
   pushAt 3147 2 8255,
   opAt 3148 (.Dup ⟨1, by decide⟩),
   opAt 3149 .GT,
   pushAt 3150 2 4345,
   opAt 3151 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
