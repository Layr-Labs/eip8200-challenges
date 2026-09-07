import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Located paths for the appended fused `ADDMOD`/conditional-subtract routine. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Fused routine entry, instructions 3110..3125, pc 5295..5316. -/
def blk3110 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3110 .JUMPDEST,
   pushAt 3111 2 8256,
   opAt 3112 (.Dup ⟨1, by decide⟩),
   opAt 3113 .SUB,
   pushAt 3114 2 8256,
   opAt 3115 (.Dup ⟨3, by decide⟩),
   opAt 3116 .SUB,
   opAt 3117 (.Swap ⟨0, by decide⟩),
   opAt 3118 (.Swap ⟨1, by decide⟩),
   opAt 3119 .POP,
   opAt 3120 (.Swap ⟨1, by decide⟩),
   opAt 3121 .POP,
   pushAt 3122 0 0,
   pushAt 3123 0 0,
   pushAt 3124 2 9440,
   opAt 3125 .MLOAD]

/-- Fused limb loop, instructions 3126..3180, pc 5317..5380. -/
def blk3126 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3126 .JUMPDEST,
   opAt 3127 (.Dup ⟨3, by decide⟩),
   opAt 3128 (.Dup ⟨1, by decide⟩),
   opAt 3129 .ADD,
   opAt 3130 .MLOAD,
   opAt 3131 (.Dup ⟨5, by decide⟩),
   opAt 3132 (.Dup ⟨2, by decide⟩),
   opAt 3133 .ADD,
   opAt 3134 .MLOAD,
   opAt 3135 (.Dup ⟨1, by decide⟩),
   opAt 3136 .ADD,
   opAt 3137 (.Dup ⟨0, by decide⟩),
   opAt 3138 (.Swap ⟨1, by decide⟩),
   opAt 3139 .GT,
   opAt 3140 (.Dup ⟨3, by decide⟩),
   opAt 3141 (.Dup ⟨2, by decide⟩),
   opAt 3142 .ADD,
   opAt 3143 (.Dup ⟨0, by decide⟩),
   opAt 3144 (.Swap ⟨2, by decide⟩),
   opAt 3145 .GT,
   opAt 3146 .OR,
   opAt 3147 (.Swap ⟨2, by decide⟩),
   opAt 3148 .POP,
   pushAt 3149 2 8256,
   opAt 3150 (.Dup ⟨2, by decide⟩),
   opAt 3151 .SUB,
   opAt 3152 .MLOAD,
   opAt 3153 (.Dup ⟨1, by decide⟩),
   opAt 3154 .SUB,
   opAt 3155 (.Dup ⟨0, by decide⟩),
   opAt 3156 (.Dup ⟨2, by decide⟩),
   opAt 3157 .LT,
   opAt 3158 (.Dup ⟨5, by decide⟩),
   opAt 3159 (.Dup ⟨2, by decide⟩),
   opAt 3160 .SUB,
   opAt 3161 (.Dup ⟨0, by decide⟩),
   opAt 3162 (.Swap ⟨2, by decide⟩),
   opAt 3163 .LT,
   opAt 3164 .OR,
   opAt 3165 (.Swap ⟨4, by decide⟩),
   opAt 3166 .POP,
   pushAt 3167 2 1088,
   opAt 3168 (.Dup ⟨3, by decide⟩),
   opAt 3169 .SUB,
   opAt 3170 .MSTORE,
   opAt 3171 (.Dup ⟨1, by decide⟩),
   opAt 3172 .MSTORE,
   pushAt 3173 1 32,
   opAt 3174 (.Swap ⟨0, by decide⟩),
   opAt 3175 .SUB,
   pushAt 3176 2 8224,
   opAt 3177 (.Dup ⟨1, by decide⟩),
   opAt 3178 .GT,
   pushAt 3179 2 5317,
   opAt 3180 .JUMPI]

/-- Fused selection and return, instructions 3181..3203, pc 5381..5411. -/
def blk3181 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3181 (.Dup ⟨1, by decide⟩),
   pushAt 3182 2 8224,
   opAt 3183 .MSTORE,
   opAt 3184 (.Dup ⟨2, by decide⟩),
   opAt 3185 .ISZERO,
   opAt 3186 (.Dup ⟨2, by decide⟩),
   opAt 3187 .OR,
   pushAt 3188 2 1088,
   opAt 3189 .MUL,
   pushAt 3190 2 8256,
   opAt 3191 .SUB,
   pushAt 3192 2 9344,
   opAt 3193 .MLOAD,
   opAt 3194 (.Swap ⟨0, by decide⟩),
   opAt 3195 (.Dup ⟨7, by decide⟩),
   opAt 3196 .MCOPY,
   opAt 3197 .POP,
   opAt 3198 .POP,
   opAt 3199 .POP,
   opAt 3200 .POP,
   opAt 3201 .POP,
   opAt 3202 .POP,
   opAt 3203 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
