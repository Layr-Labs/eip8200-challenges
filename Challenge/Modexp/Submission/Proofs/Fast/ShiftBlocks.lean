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
  [opAt 2809 .JUMPDEST,
   opAt 2810 (.Dup ⟨0, by decide⟩),
   opAt 2811 .MLOAD,
   opAt 2812 .NOT,
   opAt 2813 (.Dup ⟨2, by decide⟩),
   opAt 2814 .ADD,
   opAt 2815 (.Dup ⟨2, by decide⟩),
   opAt 2816 (.Dup ⟨1, by decide⟩),
   opAt 2817 .LT,
   opAt 2818 (.Swap ⟨2, by decide⟩),
   opAt 2819 .POP,
   opAt 2820 (.Dup ⟨1, by decide⟩),
   pushAt 2821 2 5120,
   opAt 2822 .ADD,
   opAt 2823 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2824 (.Dup ⟨0, by decide⟩),
   opAt 2825 .ISZERO,
   pushAt 2826 2 3886,
   opAt 2827 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2997 .JUMPDEST,
   opAt 2998 (.Dup ⟨0, by decide⟩),
   opAt 2999 .MLOAD,
   pushAt 3000 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3001 (.Dup ⟨5, by decide⟩),
   opAt 3002 (.Dup ⟨2, by decide⟩),
   opAt 3003 .MUL,
   opAt 3004 (.Swap ⟨1, by decide⟩),
   opAt 3005 (.Dup ⟨6, by decide⟩),
   opAt 3006 .MULMOD,
   opAt 3007 (.Dup ⟨1, by decide⟩),
   opAt 3008 (.Dup ⟨1, by decide⟩),
   opAt 3009 .LT,
   opAt 3010 .SUB,
   opAt 3011 (.Dup ⟨4, by decide⟩),
   opAt 3012 (.Dup ⟨2, by decide⟩),
   opAt 3013 .ADD,
   opAt 3014 (.Dup ⟨0, by decide⟩),
   opAt 3015 (.Swap ⟨5, by decide⟩),
   opAt 3016 .GT,
   opAt 3017 .SUB,
   opAt 3018 .SUB,
   opAt 3019 (.Dup ⟨3, by decide⟩),
   opAt 3020 (.Dup ⟨3, by decide⟩),
   opAt 3021 .MLOAD,
   opAt 3022 .ADD,
   opAt 3023 (.Dup ⟨0, by decide⟩),
   opAt 3024 (.Swap ⟨4, by decide⟩),
   opAt 3025 .GT,
   opAt 3026 .ADD,
   opAt 3027 (.Swap ⟨2, by decide⟩),
   opAt 3028 (.Dup ⟨2, by decide⟩),
   pushAt 3029 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3030 .ADD,
   opAt 3031 (.Swap ⟨2, by decide⟩),
   opAt 3032 .MSTORE,
   pushAt 3033 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3034 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3035 2 8224,
   opAt 3036 (.Dup ⟨2, by decide⟩),
   opAt 3037 .GT,
   pushAt 3038 2 4101,
   opAt 3039 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3072 .JUMPDEST,
   opAt 3073 (.Dup ⟨0, by decide⟩),
   opAt 3074 .MLOAD,
   opAt 3075 (.Dup ⟨1, by decide⟩),
   pushAt 3076 2 8256,
   opAt 3077 (.Swap ⟨0, by decide⟩),
   opAt 3078 .SUB,
   opAt 3079 .MLOAD,
   opAt 3080 (.Dup ⟨1, by decide⟩),
   opAt 3081 .ADD,
   opAt 3082 (.Dup ⟨0, by decide⟩),
   opAt 3083 (.Dup ⟨2, by decide⟩),
   opAt 3084 .GT,
   opAt 3085 (.Swap ⟨1, by decide⟩),
   opAt 3086 .POP,
   opAt 3087 (.Dup ⟨3, by decide⟩),
   opAt 3088 .ADD,
   opAt 3089 (.Dup ⟨0, by decide⟩),
   opAt 3090 (.Dup ⟨4, by decide⟩),
   opAt 3091 .GT,
   opAt 3092 (.Swap ⟨3, by decide⟩),
   opAt 3093 .POP,
   opAt 3094 (.Dup ⟨2, by decide⟩),
   opAt 3095 .MSTORE,
   opAt 3096 (.Swap ⟨0, by decide⟩),
   opAt 3097 (.Swap ⟨1, by decide⟩),
   opAt 3098 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3099 (.Swap ⟨0, by decide⟩),
   pushAt 3100 1 31, opAt 3101 .NOT,
   opAt 3102 .ADD,
   pushAt 3103 2 8255,
   opAt 3104 (.Dup ⟨1, by decide⟩),
   opAt 3105 .GT,
   pushAt 3106 2 4284,
   opAt 3107 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3129 .JUMPDEST,
   opAt 3130 (.Dup ⟨0, by decide⟩),
   opAt 3131 .MLOAD,
   opAt 3132 (.Dup ⟨1, by decide⟩),
   pushAt 3133 2 8256,
   opAt 3134 (.Swap ⟨0, by decide⟩),
   opAt 3135 .SUB,
   opAt 3136 .MLOAD,
   opAt 3137 (.Dup ⟨1, by decide⟩),
   opAt 3138 (.Dup ⟨1, by decide⟩),
   opAt 3139 .GT,
   opAt 3140 (.Swap ⟨1, by decide⟩),
   opAt 3141 .SUB,
   opAt 3142 (.Dup ⟨3, by decide⟩),
   opAt 3143 (.Dup ⟨1, by decide⟩),
   opAt 3144 .LT,
   opAt 3145 (.Swap ⟨0, by decide⟩),
   opAt 3146 (.Dup ⟨4, by decide⟩),
   opAt 3147 (.Swap ⟨0, by decide⟩),
   opAt 3148 .SUB,
   opAt 3149 (.Dup ⟨3, by decide⟩),
   opAt 3150 .MSTORE,
   opAt 3151 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3152 (.Swap ⟨1, by decide⟩),
   opAt 3153 .POP,
   pushAt 3154 1 31, opAt 3155 .NOT,
   opAt 3156 .ADD,
   pushAt 3157 2 8255,
   opAt 3158 (.Dup ⟨1, by decide⟩),
   opAt 3159 .GT,
   pushAt 3160 2 4360,
   opAt 3161 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
