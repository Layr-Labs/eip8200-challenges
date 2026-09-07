import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Located paths for the appended fused `ADDMOD`/conditional-subtract routine. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Fused routine entry, instructions 3036..3051, pc 5029..5050. -/
def blk3036 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3036 .JUMPDEST,
   pushAt 3037 4 8256,
   opAt 3038 (.Dup ⟨0, by decide⟩),
   opAt 3039 (.Swap ⟨1, by decide⟩),
   opAt 3040 .SUB,
   opAt 3041 (.Swap ⟨1, by decide⟩),
   opAt 3042 .SUB,
   opAt 3043 (.Swap ⟨0, by decide⟩),
   opAt 3044 .JUMPDEST,
   opAt 3045 .JUMPDEST,
   opAt 3046 .JUMPDEST,
   opAt 3047 .JUMPDEST,
   pushAt 3048 0 0,
   pushAt 3049 0 0,
   pushAt 3050 2 9440,
   opAt 3051 .MLOAD]

/-- Fused limb loop, instructions 3052..3106, pc 5051..5114. -/
def blk3052 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3052 .JUMPDEST,
   opAt 3053 (.Dup ⟨3, by decide⟩),
   opAt 3054 (.Dup ⟨1, by decide⟩),
   opAt 3055 .ADD,
   opAt 3056 .MLOAD,
   opAt 3057 (.Dup ⟨5, by decide⟩),
   opAt 3058 (.Dup ⟨2, by decide⟩),
   opAt 3059 .ADD,
   opAt 3060 .MLOAD,
   opAt 3061 (.Dup ⟨1, by decide⟩),
   opAt 3062 .ADD,
   opAt 3063 (.Dup ⟨0, by decide⟩),
   opAt 3064 (.Swap ⟨1, by decide⟩),
   opAt 3065 .GT,
   opAt 3066 (.Dup ⟨3, by decide⟩),
   opAt 3067 (.Dup ⟨2, by decide⟩),
   opAt 3068 .ADD,
   opAt 3069 (.Dup ⟨0, by decide⟩),
   opAt 3070 (.Swap ⟨2, by decide⟩),
   opAt 3071 .GT,
   opAt 3072 .OR,
   opAt 3073 (.Swap ⟨2, by decide⟩),
   opAt 3074 .POP,
   pushAt 3075 2 8256,
   opAt 3076 (.Dup ⟨2, by decide⟩),
   opAt 3077 .SUB,
   opAt 3078 .MLOAD,
   opAt 3079 (.Dup ⟨1, by decide⟩),
   opAt 3080 .SUB,
   opAt 3081 (.Dup ⟨0, by decide⟩),
   opAt 3082 (.Dup ⟨2, by decide⟩),
   opAt 3083 .LT,
   opAt 3084 (.Dup ⟨5, by decide⟩),
   opAt 3085 (.Dup ⟨2, by decide⟩),
   opAt 3086 .SUB,
   opAt 3087 (.Dup ⟨0, by decide⟩),
   opAt 3088 (.Swap ⟨2, by decide⟩),
   opAt 3089 .LT,
   opAt 3090 .OR,
   opAt 3091 (.Swap ⟨4, by decide⟩),
   opAt 3092 .POP,
   pushAt 3093 2 1088,
   opAt 3094 (.Dup ⟨3, by decide⟩),
   opAt 3095 .SUB,
   opAt 3096 .MSTORE,
   opAt 3097 (.Dup ⟨1, by decide⟩),
   opAt 3098 .MSTORE,
   pushAt 3099 1 32,
   opAt 3100 (.Swap ⟨0, by decide⟩),
   opAt 3101 .SUB,
   pushAt 3102 2 8224,
   opAt 3103 (.Dup ⟨1, by decide⟩),
   opAt 3104 .GT,
   pushAt 3105 2 5051,
   opAt 3106 .JUMPI]

/-- Fused selection and return, live instructions 3107..3125, pc 5115..5141; trailing padding is not executed. -/
def blk3107 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3107 .POP,
   opAt 3108 (.Dup ⟨0, by decide⟩),
   pushAt 3109 2 8224,
   opAt 3110 .MSTORE,
   opAt 3111 (.Swap ⟨0, by decide⟩),
   opAt 3112 .ISZERO,
   opAt 3113 .OR,
   pushAt 3114 2 1088,
   opAt 3115 .MUL,
   pushAt 3116 2 8256,
   opAt 3117 .SUB,
   opAt 3118 (.Swap ⟨1, by decide⟩),
   opAt 3119 .POP,
   opAt 3120 .POP,
   pushAt 3121 2 9344,
   opAt 3122 .MLOAD,
   opAt 3123 (.Swap ⟨1, by decide⟩),
   opAt 3124 .MCOPY,
   opAt 3125 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
