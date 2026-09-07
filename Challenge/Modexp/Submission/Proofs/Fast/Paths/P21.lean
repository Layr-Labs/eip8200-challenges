import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Located paths for the appended fused `ADDMOD`/conditional-subtract routine. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Fused routine entry, instructions 3028..3043, pc 5029..5050. -/
def blk3036 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3028 .JUMPDEST,
   pushAt 3029 2 8256,
   opAt 3030 (.Dup ⟨1, by decide⟩),
   opAt 3031 .SUB,
   pushAt 3032 2 8256,
   opAt 3033 (.Dup ⟨3, by decide⟩),
   opAt 3034 .SUB,
   opAt 3035 (.Swap ⟨0, by decide⟩),
   opAt 3036 (.Swap ⟨1, by decide⟩),
   opAt 3037 .POP,
   opAt 3038 (.Swap ⟨1, by decide⟩),
   opAt 3039 .POP,
   pushAt 3040 0 0,
   pushAt 3041 0 0,
   pushAt 3042 2 9440,
   opAt 3043 .MLOAD]

/-- Fused limb loop, instructions 3044..3098, pc 5051..5114. -/
def blk3052 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3044 .JUMPDEST,
   opAt 3045 (.Dup ⟨3, by decide⟩),
   opAt 3046 (.Dup ⟨1, by decide⟩),
   opAt 3047 .ADD,
   opAt 3048 .MLOAD,
   opAt 3049 (.Dup ⟨5, by decide⟩),
   opAt 3050 (.Dup ⟨2, by decide⟩),
   opAt 3051 .ADD,
   opAt 3052 .MLOAD,
   opAt 3053 (.Dup ⟨1, by decide⟩),
   opAt 3054 .ADD,
   opAt 3055 (.Dup ⟨0, by decide⟩),
   opAt 3056 (.Swap ⟨1, by decide⟩),
   opAt 3057 .GT,
   opAt 3058 (.Dup ⟨3, by decide⟩),
   opAt 3059 (.Dup ⟨2, by decide⟩),
   opAt 3060 .ADD,
   opAt 3061 (.Dup ⟨0, by decide⟩),
   opAt 3062 (.Swap ⟨2, by decide⟩),
   opAt 3063 .GT,
   opAt 3064 .OR,
   opAt 3065 (.Swap ⟨2, by decide⟩),
   opAt 3066 .POP,
   pushAt 3067 2 8256,
   opAt 3068 (.Dup ⟨2, by decide⟩),
   opAt 3069 .SUB,
   opAt 3070 .MLOAD,
   opAt 3071 (.Dup ⟨1, by decide⟩),
   opAt 3072 .SUB,
   opAt 3073 (.Dup ⟨0, by decide⟩),
   opAt 3074 (.Dup ⟨2, by decide⟩),
   opAt 3075 .LT,
   opAt 3076 (.Dup ⟨5, by decide⟩),
   opAt 3077 (.Dup ⟨2, by decide⟩),
   opAt 3078 .SUB,
   opAt 3079 (.Dup ⟨0, by decide⟩),
   opAt 3080 (.Swap ⟨2, by decide⟩),
   opAt 3081 .LT,
   opAt 3082 .OR,
   opAt 3083 (.Swap ⟨4, by decide⟩),
   opAt 3084 .POP,
   pushAt 3085 2 1088,
   opAt 3086 (.Dup ⟨3, by decide⟩),
   opAt 3087 .SUB,
   opAt 3088 .MSTORE,
   opAt 3089 (.Dup ⟨1, by decide⟩),
   opAt 3090 .MSTORE,
   pushAt 3091 1 32,
   opAt 3092 (.Swap ⟨0, by decide⟩),
   opAt 3093 .SUB,
   pushAt 3094 2 8224,
   opAt 3095 (.Dup ⟨1, by decide⟩),
   opAt 3096 .GT,
   pushAt 3097 2 5051,
   opAt 3098 .JUMPI]

/-- Fused selection and return, instructions 3099..3121, pc 5115..5145. -/
def blk3107 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3099 (.Dup ⟨1, by decide⟩),
   pushAt 3100 2 8224,
   opAt 3101 .MSTORE,
   opAt 3102 (.Dup ⟨2, by decide⟩),
   opAt 3103 .ISZERO,
   opAt 3104 (.Dup ⟨2, by decide⟩),
   opAt 3105 .OR,
   pushAt 3106 2 1088,
   opAt 3107 .MUL,
   pushAt 3108 2 8256,
   opAt 3109 .SUB,
   pushAt 3110 2 9344,
   opAt 3111 .MLOAD,
   opAt 3112 (.Swap ⟨0, by decide⟩),
   opAt 3113 (.Dup ⟨7, by decide⟩),
   opAt 3114 .MCOPY,
   opAt 3115 .POP,
   opAt 3116 .POP,
   opAt 3117 .POP,
   opAt 3118 .POP,
   opAt 3119 .POP,
   opAt 3120 .POP,
   opAt 3121 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
