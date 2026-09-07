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
  [opAt 3120 .JUMPDEST,
   pushAt 3121 4 8256,
   opAt 3122 (.Dup ⟨0, by decide⟩),
   opAt 3123 (.Swap ⟨1, by decide⟩),
   opAt 3124 .SUB,
   opAt 3125 (.Swap ⟨1, by decide⟩),
   opAt 3126 .SUB,
   opAt 3127 (.Swap ⟨0, by decide⟩),
   opAt 3128 .JUMPDEST,
   opAt 3129 .JUMPDEST,
   opAt 3130 .JUMPDEST,
   opAt 3131 .JUMPDEST,
   pushAt 3132 0 0,
   pushAt 3133 0 0,
   pushAt 3134 2 9440,
   opAt 3135 .MLOAD]

/-- Fused limb loop, instructions 3136..3190, pc 5327..5390. -/
def blk3136 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3136 .JUMPDEST,
   opAt 3137 (.Dup ⟨3, by decide⟩),
   opAt 3138 (.Dup ⟨1, by decide⟩),
   opAt 3139 .ADD,
   opAt 3140 .MLOAD,
   opAt 3141 (.Dup ⟨5, by decide⟩),
   opAt 3142 (.Dup ⟨2, by decide⟩),
   opAt 3143 .ADD,
   opAt 3144 .MLOAD,
   opAt 3145 (.Dup ⟨1, by decide⟩),
   opAt 3146 .ADD,
   opAt 3147 (.Dup ⟨0, by decide⟩),
   opAt 3148 (.Swap ⟨1, by decide⟩),
   opAt 3149 .GT,
   opAt 3150 (.Dup ⟨3, by decide⟩),
   opAt 3151 (.Dup ⟨2, by decide⟩),
   opAt 3152 .ADD,
   opAt 3153 (.Dup ⟨0, by decide⟩),
   opAt 3154 (.Swap ⟨2, by decide⟩),
   opAt 3155 .GT,
   opAt 3156 .OR,
   opAt 3157 (.Swap ⟨2, by decide⟩),
   opAt 3158 .POP,
   pushAt 3159 2 8256,
   opAt 3160 (.Dup ⟨2, by decide⟩),
   opAt 3161 .SUB,
   opAt 3162 .MLOAD,
   opAt 3163 (.Dup ⟨1, by decide⟩),
   opAt 3164 .SUB,
   opAt 3165 (.Dup ⟨0, by decide⟩),
   opAt 3166 (.Dup ⟨2, by decide⟩),
   opAt 3167 .LT,
   opAt 3168 (.Dup ⟨5, by decide⟩),
   opAt 3169 (.Dup ⟨2, by decide⟩),
   opAt 3170 .SUB,
   opAt 3171 (.Dup ⟨0, by decide⟩),
   opAt 3172 (.Swap ⟨2, by decide⟩),
   opAt 3173 .LT,
   opAt 3174 .OR,
   opAt 3175 (.Swap ⟨4, by decide⟩),
   opAt 3176 .POP,
   pushAt 3177 2 1088,
   opAt 3178 (.Dup ⟨3, by decide⟩),
   opAt 3179 .SUB,
   opAt 3180 .MSTORE,
   opAt 3181 (.Dup ⟨1, by decide⟩),
   opAt 3182 .MSTORE,
   pushAt 3183 1 32,
   opAt 3184 (.Swap ⟨0, by decide⟩),
   opAt 3185 .SUB,
   pushAt 3186 2 8224,
   opAt 3187 (.Dup ⟨1, by decide⟩),
   opAt 3188 .GT,
   pushAt 3189 2 5327,
   opAt 3190 .JUMPI]

/-- Fused selection and return, live instructions 3191..3209, pc 5391..5417; trailing padding is not executed. -/
def blk3191 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3191 .POP,
   opAt 3192 (.Dup ⟨0, by decide⟩),
   pushAt 3193 2 8224,
   opAt 3194 .MSTORE,
   opAt 3195 (.Swap ⟨0, by decide⟩),
   opAt 3196 .ISZERO,
   opAt 3197 .OR,
   pushAt 3198 2 1088,
   opAt 3199 .MUL,
   pushAt 3200 2 8256,
   opAt 3201 .SUB,
   opAt 3202 (.Swap ⟨1, by decide⟩),
   opAt 3203 .POP,
   opAt 3204 .POP,
   pushAt 3205 2 9344,
   opAt 3206 .MLOAD,
   opAt 3207 (.Swap ⟨1, by decide⟩),
   opAt 3208 .MCOPY,
   opAt 3209 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
