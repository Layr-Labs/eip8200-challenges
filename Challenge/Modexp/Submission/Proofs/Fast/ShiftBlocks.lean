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
  [opAt 2798 .JUMPDEST,
   opAt 2799 (.Dup ⟨0, by decide⟩),
   opAt 2800 .MLOAD,
   opAt 2801 .NOT,
   opAt 2802 (.Dup ⟨2, by decide⟩),
   opAt 2803 .ADD,
   opAt 2804 (.Dup ⟨2, by decide⟩),
   opAt 2805 (.Dup ⟨1, by decide⟩),
   opAt 2806 .LT,
   opAt 2807 (.Swap ⟨2, by decide⟩),
   opAt 2808 .POP,
   opAt 2809 (.Dup ⟨1, by decide⟩),
   pushAt 2810 2 5120,
   opAt 2811 .ADD,
   opAt 2812 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2813 (.Dup ⟨0, by decide⟩),
   opAt 2814 .ISZERO,
   pushAt 2815 2 3896,
   opAt 2816 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2987 .JUMPDEST,
   opAt 2988 (.Dup ⟨0, by decide⟩),
   opAt 2989 .MLOAD,
   pushAt 2990 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2991 (.Dup ⟨5, by decide⟩),
   opAt 2992 (.Dup ⟨2, by decide⟩),
   opAt 2993 .MUL,
   opAt 2994 (.Swap ⟨1, by decide⟩),
   opAt 2995 (.Dup ⟨6, by decide⟩),
   opAt 2996 .MULMOD,
   opAt 2997 (.Dup ⟨1, by decide⟩),
   opAt 2998 (.Dup ⟨1, by decide⟩),
   opAt 2999 .LT,
   opAt 3000 .SUB,
   opAt 3001 (.Dup ⟨4, by decide⟩),
   opAt 3002 (.Dup ⟨2, by decide⟩),
   opAt 3003 .ADD,
   opAt 3004 (.Dup ⟨0, by decide⟩),
   opAt 3005 (.Swap ⟨5, by decide⟩),
   opAt 3006 .GT,
   opAt 3007 .SUB,
   opAt 3008 .SUB,
   opAt 3009 (.Dup ⟨3, by decide⟩),
   opAt 3010 (.Dup ⟨3, by decide⟩),
   opAt 3011 .MLOAD,
   opAt 3012 .ADD,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 (.Swap ⟨4, by decide⟩),
   opAt 3015 .GT,
   opAt 3016 .ADD,
   opAt 3017 (.Swap ⟨2, by decide⟩),
   opAt 3018 (.Dup ⟨2, by decide⟩),
   pushAt 3019 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3020 .ADD,
   opAt 3021 (.Swap ⟨2, by decide⟩),
   opAt 3022 .MSTORE,
   pushAt 3023 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3024 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3025 2 8224,
   opAt 3026 (.Dup ⟨2, by decide⟩),
   opAt 3027 .GT,
   pushAt 3028 2 4115,
   opAt 3029 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3062 .JUMPDEST,
   opAt 3063 (.Dup ⟨0, by decide⟩),
   opAt 3064 .MLOAD,
   opAt 3065 (.Dup ⟨1, by decide⟩),
   pushAt 3066 2 8256,
   opAt 3067 (.Swap ⟨0, by decide⟩),
   opAt 3068 .SUB,
   opAt 3069 .MLOAD,
   opAt 3070 (.Dup ⟨1, by decide⟩),
   opAt 3071 .ADD,
   opAt 3072 (.Dup ⟨0, by decide⟩),
   opAt 3073 (.Dup ⟨2, by decide⟩),
   opAt 3074 .GT,
   opAt 3075 (.Swap ⟨1, by decide⟩),
   opAt 3076 .POP,
   opAt 3077 (.Dup ⟨3, by decide⟩),
   opAt 3078 .ADD,
   opAt 3079 (.Dup ⟨0, by decide⟩),
   opAt 3080 (.Dup ⟨4, by decide⟩),
   opAt 3081 .GT,
   opAt 3082 (.Swap ⟨3, by decide⟩),
   opAt 3083 .POP,
   opAt 3084 (.Dup ⟨2, by decide⟩),
   opAt 3085 .MSTORE,
   opAt 3086 (.Swap ⟨0, by decide⟩),
   opAt 3087 (.Swap ⟨1, by decide⟩),
   opAt 3088 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3089 (.Swap ⟨0, by decide⟩),
   pushAt 3090 1 31, opAt 3091 .NOT,
   opAt 3092 .ADD,
   pushAt 3093 2 8255,
   opAt 3094 (.Dup ⟨1, by decide⟩),
   opAt 3095 .GT,
   pushAt 3096 2 4298,
   opAt 3097 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3119 .JUMPDEST,
   opAt 3120 (.Dup ⟨0, by decide⟩),
   opAt 3121 .MLOAD,
   pushAt 3122 2 8256,
   opAt 3123 (.Dup ⟨2, by decide⟩),
   opAt 3124 .SUB,
   opAt 3125 .MLOAD,
   opAt 3126 (.Dup ⟨1, by decide⟩),
   opAt 3127 (.Dup ⟨1, by decide⟩),
   opAt 3128 .GT,
   opAt 3129 (.Swap ⟨1, by decide⟩),
   opAt 3130 .SUB,
   opAt 3131 (.Dup ⟨3, by decide⟩),
   opAt 3132 (.Dup ⟨1, by decide⟩),
   opAt 3133 .LT,
   opAt 3134 (.Swap ⟨0, by decide⟩),
   opAt 3135 (.Dup ⟨4, by decide⟩),
   opAt 3136 (.Swap ⟨0, by decide⟩),
   opAt 3137 .SUB,
   opAt 3138 (.Dup ⟨3, by decide⟩),
   opAt 3139 .MSTORE,
   opAt 3140 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3141 (.Swap ⟨1, by decide⟩),
   opAt 3142 .POP,
   pushAt 3143 1 31, opAt 3144 .NOT,
   opAt 3145 .ADD,
   pushAt 3146 2 8255,
   opAt 3147 (.Dup ⟨1, by decide⟩),
   opAt 3148 .GT,
   pushAt 3149 2 4374,
   opAt 3150 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
