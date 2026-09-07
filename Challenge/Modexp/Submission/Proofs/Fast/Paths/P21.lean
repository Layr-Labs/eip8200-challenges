import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Located paths for the appended fused `ADDMOD`/conditional-subtract routine. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Fused routine entry, instructions 3120..3135, pc 5305..5326. -/
def blk3120 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3085 .JUMPDEST,
   pushAt 3086 2 8256,
   opAt 3087 (.Dup ⟨1, by decide⟩),
   opAt 3088 .SUB,
   pushAt 3089 2 8256,
   opAt 3090 (.Dup ⟨3, by decide⟩),
   opAt 3091 .SUB,
   opAt 3092 (.Swap ⟨0, by decide⟩),
   opAt 3093 (.Swap ⟨1, by decide⟩),
   opAt 3094 .POP,
   opAt 3095 (.Swap ⟨1, by decide⟩),
   opAt 3096 .POP,
   pushAt 3097 0 0,
   pushAt 3098 0 0,
   pushAt 3099 2 9440,
   opAt 3100 .MLOAD]

/-- Fused limb loop, instructions 3136..3190, pc 5327..5390. -/
def blk3136 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3101 .JUMPDEST,
   opAt 3102 (.Dup ⟨3, by decide⟩),
   opAt 3103 (.Dup ⟨1, by decide⟩),
   opAt 3104 .ADD,
   opAt 3105 .MLOAD,
   opAt 3106 (.Dup ⟨5, by decide⟩),
   opAt 3107 (.Dup ⟨2, by decide⟩),
   opAt 3108 .ADD,
   opAt 3109 .MLOAD,
   opAt 3110 (.Dup ⟨1, by decide⟩),
   opAt 3111 .ADD,
   opAt 3112 (.Dup ⟨0, by decide⟩),
   opAt 3113 (.Swap ⟨1, by decide⟩),
   opAt 3114 .GT,
   opAt 3115 (.Dup ⟨3, by decide⟩),
   opAt 3116 (.Dup ⟨2, by decide⟩),
   opAt 3117 .ADD,
   opAt 3118 (.Dup ⟨0, by decide⟩),
   opAt 3119 (.Swap ⟨2, by decide⟩),
   opAt 3120 .GT,
   opAt 3121 .OR,
   opAt 3122 (.Swap ⟨2, by decide⟩),
   opAt 3123 .POP,
   pushAt 3124 2 8256,
   opAt 3125 (.Dup ⟨2, by decide⟩),
   opAt 3126 .SUB,
   opAt 3127 .MLOAD,
   opAt 3128 (.Dup ⟨1, by decide⟩),
   opAt 3129 .SUB,
   opAt 3130 (.Dup ⟨0, by decide⟩),
   opAt 3131 (.Dup ⟨2, by decide⟩),
   opAt 3132 .LT,
   opAt 3133 (.Dup ⟨5, by decide⟩),
   opAt 3134 (.Dup ⟨2, by decide⟩),
   opAt 3135 .SUB,
   opAt 3136 (.Dup ⟨0, by decide⟩),
   opAt 3137 (.Swap ⟨2, by decide⟩),
   opAt 3138 .LT,
   opAt 3139 .OR,
   opAt 3140 (.Swap ⟨4, by decide⟩),
   opAt 3141 .POP,
   pushAt 3142 2 1088,
   opAt 3143 (.Dup ⟨3, by decide⟩),
   opAt 3144 .SUB,
   opAt 3145 .MSTORE,
   opAt 3146 (.Dup ⟨1, by decide⟩),
   opAt 3147 .MSTORE,
   pushAt 3148 1 32,
   opAt 3149 (.Swap ⟨0, by decide⟩),
   opAt 3150 .SUB,
   pushAt 3151 2 8224,
   opAt 3152 (.Dup ⟨1, by decide⟩),
   opAt 3153 .GT,
   pushAt 3154 2 5292,
   opAt 3155 .JUMPI]

/-- Fused selection and return, instructions 3191..3213, pc 5391..5421. -/
def blk3191 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3156 (.Dup ⟨1, by decide⟩),
   pushAt 3157 2 8224,
   opAt 3158 .MSTORE,
   opAt 3159 (.Dup ⟨2, by decide⟩),
   opAt 3160 .ISZERO,
   opAt 3161 (.Dup ⟨2, by decide⟩),
   opAt 3162 .OR,
   pushAt 3163 2 1088,
   opAt 3164 .MUL,
   pushAt 3165 2 8256,
   opAt 3166 .SUB,
   pushAt 3167 2 9344,
   opAt 3168 .MLOAD,
   opAt 3169 (.Swap ⟨0, by decide⟩),
   opAt 3170 (.Dup ⟨7, by decide⟩),
   opAt 3171 .MCOPY,
   opAt 3172 .POP,
   opAt 3173 .POP,
   opAt 3174 .POP,
   opAt 3175 .POP,
   opAt 3176 .POP,
   opAt 3177 .POP,
   opAt 3178 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
