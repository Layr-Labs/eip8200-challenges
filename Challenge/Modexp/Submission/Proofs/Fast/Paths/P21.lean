import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Located paths for the appended fused `ADDMOD`/conditional-subtract routine. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 3084..3096, pc 5267..5285. -/
def blk3084 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3084 .JUMPDEST,
   pushAt 3085 2 8256,
   opAt 3086 (.Swap ⟨0, by decide⟩),
   opAt 3087 .SUB,
   opAt 3088 (.Swap ⟨0, by decide⟩),
   pushAt 3089 2 8256,
   opAt 3090 (.Swap ⟨0, by decide⟩),
   opAt 3091 .SUB,
   opAt 3092 (.Swap ⟨0, by decide⟩),
   pushAt 3093 0 0,
   pushAt 3094 0 0,
   pushAt 3095 2 9440,
   opAt 3096 .MLOAD]

/-- Instructions 3097..3151, pc 5286..5349. -/
def blk3097 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3097 .JUMPDEST,
   opAt 3098 (.Dup ⟨3, by decide⟩),
   opAt 3099 (.Dup ⟨1, by decide⟩),
   opAt 3100 .ADD,
   opAt 3101 .MLOAD,
   opAt 3102 (.Dup ⟨5, by decide⟩),
   opAt 3103 (.Dup ⟨2, by decide⟩),
   opAt 3104 .ADD,
   opAt 3105 .MLOAD,
   opAt 3106 (.Dup ⟨1, by decide⟩),
   opAt 3107 .ADD,
   opAt 3108 (.Dup ⟨0, by decide⟩),
   opAt 3109 (.Swap ⟨1, by decide⟩),
   opAt 3110 .GT,
   opAt 3111 (.Dup ⟨3, by decide⟩),
   opAt 3112 (.Dup ⟨2, by decide⟩),
   opAt 3113 .ADD,
   opAt 3114 (.Dup ⟨0, by decide⟩),
   opAt 3115 (.Swap ⟨2, by decide⟩),
   opAt 3116 .GT,
   opAt 3117 .OR,
   opAt 3118 (.Swap ⟨2, by decide⟩),
   opAt 3119 .POP,
   pushAt 3120 2 8256,
   opAt 3121 (.Dup ⟨2, by decide⟩),
   opAt 3122 .SUB,
   opAt 3123 .MLOAD,
   opAt 3124 (.Dup ⟨1, by decide⟩),
   opAt 3125 .SUB,
   opAt 3126 (.Dup ⟨0, by decide⟩),
   opAt 3127 (.Dup ⟨2, by decide⟩),
   opAt 3128 .LT,
   opAt 3129 (.Dup ⟨5, by decide⟩),
   opAt 3130 (.Dup ⟨2, by decide⟩),
   opAt 3131 .SUB,
   opAt 3132 (.Dup ⟨0, by decide⟩),
   opAt 3133 (.Swap ⟨2, by decide⟩),
   opAt 3134 .LT,
   opAt 3135 .OR,
   opAt 3136 (.Swap ⟨4, by decide⟩),
   opAt 3137 .POP,
   pushAt 3138 2 1088,
   opAt 3139 (.Dup ⟨3, by decide⟩),
   opAt 3140 .SUB,
   opAt 3141 .MSTORE,
   opAt 3142 (.Dup ⟨1, by decide⟩),
   opAt 3143 .MSTORE,
   pushAt 3144 1 32,
   opAt 3145 (.Swap ⟨0, by decide⟩),
   opAt 3146 .SUB,
   pushAt 3147 2 8224,
   opAt 3148 (.Dup ⟨1, by decide⟩),
   opAt 3149 .GT,
   pushAt 3150 2 5286,
   opAt 3151 .JUMPI]

/-- Instructions 3152..3174, pc 5350..5380. -/
def blk3152 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3152 (.Dup ⟨1, by decide⟩),
   pushAt 3153 2 8224,
   opAt 3154 .MSTORE,
   opAt 3155 (.Dup ⟨2, by decide⟩),
   opAt 3156 .ISZERO,
   opAt 3157 (.Dup ⟨2, by decide⟩),
   opAt 3158 .OR,
   pushAt 3159 2 1088,
   opAt 3160 .MUL,
   pushAt 3161 2 8256,
   opAt 3162 .SUB,
   pushAt 3163 2 9344,
   opAt 3164 .MLOAD,
   opAt 3165 (.Swap ⟨0, by decide⟩),
   opAt 3166 (.Dup ⟨7, by decide⟩),
   opAt 3167 .MCOPY,
   opAt 3168 .POP,
   opAt 3169 .POP,
   opAt 3170 .POP,
   opAt 3171 .POP,
   opAt 3172 .POP,
   opAt 3173 .POP,
   opAt 3174 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
