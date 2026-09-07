import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Located paths for the appended fused `ADDMOD`/conditional-subtract routine. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Fused routine entry, instructions 3084..3099, pc 5267..5288. -/
def blk3085 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3084 .JUMPDEST,
   pushAt 3085 2 8256,
   opAt 3086 (.Dup ⟨1, by decide⟩),
   opAt 3087 .SUB,
   pushAt 3088 2 8256,
   opAt 3089 (.Dup ⟨3, by decide⟩),
   opAt 3090 .SUB,
   opAt 3091 (.Swap ⟨0, by decide⟩),
   opAt 3092 (.Swap ⟨1, by decide⟩),
   opAt 3093 .POP,
   opAt 3094 (.Swap ⟨1, by decide⟩),
   opAt 3095 .POP,
   pushAt 3096 0 0,
   pushAt 3097 0 0,
   pushAt 3098 2 9440,
   opAt 3099 .MLOAD]

/-- Fused limb loop, instructions 3100..3154, pc 5289..5352. -/
def blk3101 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3100 .JUMPDEST,
   opAt 3101 (.Dup ⟨3, by decide⟩),
   opAt 3102 (.Dup ⟨1, by decide⟩),
   opAt 3103 .ADD,
   opAt 3104 .MLOAD,
   opAt 3105 (.Dup ⟨5, by decide⟩),
   opAt 3106 (.Dup ⟨2, by decide⟩),
   opAt 3107 .ADD,
   opAt 3108 .MLOAD,
   opAt 3109 (.Dup ⟨1, by decide⟩),
   opAt 3110 .ADD,
   opAt 3111 (.Dup ⟨0, by decide⟩),
   opAt 3112 (.Swap ⟨1, by decide⟩),
   opAt 3113 .GT,
   opAt 3114 (.Dup ⟨3, by decide⟩),
   opAt 3115 (.Dup ⟨2, by decide⟩),
   opAt 3116 .ADD,
   opAt 3117 (.Dup ⟨0, by decide⟩),
   opAt 3118 (.Swap ⟨2, by decide⟩),
   opAt 3119 .GT,
   opAt 3120 .OR,
   opAt 3121 (.Swap ⟨2, by decide⟩),
   opAt 3122 .POP,
   pushAt 3123 2 8256,
   opAt 3124 (.Dup ⟨2, by decide⟩),
   opAt 3125 .SUB,
   opAt 3126 .MLOAD,
   opAt 3127 (.Dup ⟨1, by decide⟩),
   opAt 3128 .SUB,
   opAt 3129 (.Dup ⟨0, by decide⟩),
   opAt 3130 (.Dup ⟨2, by decide⟩),
   opAt 3131 .LT,
   opAt 3132 (.Dup ⟨5, by decide⟩),
   opAt 3133 (.Dup ⟨2, by decide⟩),
   opAt 3134 .SUB,
   opAt 3135 (.Dup ⟨0, by decide⟩),
   opAt 3136 (.Swap ⟨2, by decide⟩),
   opAt 3137 .LT,
   opAt 3138 .OR,
   opAt 3139 (.Swap ⟨4, by decide⟩),
   opAt 3140 .POP,
   pushAt 3141 2 1088,
   opAt 3142 (.Dup ⟨3, by decide⟩),
   opAt 3143 .SUB,
   opAt 3144 .MSTORE,
   opAt 3145 (.Dup ⟨1, by decide⟩),
   opAt 3146 .MSTORE,
   pushAt 3147 1 32,
   opAt 3148 (.Swap ⟨0, by decide⟩),
   opAt 3149 .SUB,
   pushAt 3150 2 8224,
   opAt 3151 (.Dup ⟨1, by decide⟩),
   opAt 3152 .GT,
   pushAt 3153 2 5289,
   opAt 3154 .JUMPI]

/-- Fused selection and return, instructions 3155..3177, pc 5353..5383. -/
def blk3156 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3155 (.Dup ⟨1, by decide⟩),
   pushAt 3156 2 8224,
   opAt 3157 .MSTORE,
   opAt 3158 (.Dup ⟨2, by decide⟩),
   opAt 3159 .ISZERO,
   opAt 3160 (.Dup ⟨2, by decide⟩),
   opAt 3161 .OR,
   pushAt 3162 2 1088,
   opAt 3163 .MUL,
   pushAt 3164 2 8256,
   opAt 3165 .SUB,
   pushAt 3166 2 9344,
   opAt 3167 .MLOAD,
   opAt 3168 (.Swap ⟨0, by decide⟩),
   opAt 3169 (.Dup ⟨7, by decide⟩),
   opAt 3170 .MCOPY,
   opAt 3171 .POP,
   opAt 3172 .POP,
   opAt 3173 .POP,
   opAt 3174 .POP,
   opAt 3175 .POP,
   opAt 3176 .POP,
   opAt 3177 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
