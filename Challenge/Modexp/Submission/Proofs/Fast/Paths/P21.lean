import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Located paths for the appended fused `ADDMOD`/conditional-subtract routine. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Fused routine entry, instructions 3084..3099, pc 4569..4590. -/
def blk3085 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3003 .JUMPDEST,
   pushAt 3004 2 8256,
   opAt 3005 (.Dup ⟨1, by decide⟩),
   opAt 3006 .SUB,
   pushAt 3007 2 8256,
   opAt 3008 (.Dup ⟨3, by decide⟩),
   opAt 3009 .SUB,
   opAt 3010 (.Swap ⟨0, by decide⟩),
   opAt 3011 (.Swap ⟨1, by decide⟩),
   opAt 3012 .POP,
   opAt 3013 (.Swap ⟨1, by decide⟩),
   opAt 3014 .POP,
   pushAt 3015 0 0,
   pushAt 3016 0 0,
   pushAt 3017 2 9440,
   opAt 3018 .MLOAD]

/-- Fused limb loop, instructions 3100..3154, pc 4591..4654. -/
def blk3101 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3019 .JUMPDEST,
   opAt 3020 (.Dup ⟨3, by decide⟩),
   opAt 3021 (.Dup ⟨1, by decide⟩),
   opAt 3022 .ADD,
   opAt 3023 .MLOAD,
   opAt 3024 (.Dup ⟨5, by decide⟩),
   opAt 3025 (.Dup ⟨2, by decide⟩),
   opAt 3026 .ADD,
   opAt 3027 .MLOAD,
   opAt 3028 (.Dup ⟨1, by decide⟩),
   opAt 3029 .ADD,
   opAt 3030 (.Dup ⟨0, by decide⟩),
   opAt 3031 (.Swap ⟨1, by decide⟩),
   opAt 3032 .GT,
   opAt 3033 (.Dup ⟨3, by decide⟩),
   opAt 3034 (.Dup ⟨2, by decide⟩),
   opAt 3035 .ADD,
   opAt 3036 (.Dup ⟨0, by decide⟩),
   opAt 3037 (.Swap ⟨2, by decide⟩),
   opAt 3038 .GT,
   opAt 3039 .OR,
   opAt 3040 (.Swap ⟨2, by decide⟩),
   opAt 3041 .POP,
   pushAt 3042 2 8256,
   opAt 3043 (.Dup ⟨2, by decide⟩),
   opAt 3044 .SUB,
   opAt 3045 .MLOAD,
   opAt 3046 (.Dup ⟨1, by decide⟩),
   opAt 3047 .SUB,
   opAt 3048 (.Dup ⟨0, by decide⟩),
   opAt 3049 (.Dup ⟨2, by decide⟩),
   opAt 3050 .LT,
   opAt 3051 (.Dup ⟨5, by decide⟩),
   opAt 3052 (.Dup ⟨2, by decide⟩),
   opAt 3053 .SUB,
   opAt 3054 (.Dup ⟨0, by decide⟩),
   opAt 3055 (.Swap ⟨2, by decide⟩),
   opAt 3056 .LT,
   opAt 3057 .OR,
   opAt 3058 (.Swap ⟨4, by decide⟩),
   opAt 3059 .POP,
   pushAt 3060 2 1088,
   opAt 3061 (.Dup ⟨3, by decide⟩),
   opAt 3062 .SUB,
   opAt 3063 .MSTORE,
   opAt 3064 (.Dup ⟨1, by decide⟩),
   opAt 3065 .MSTORE,
   pushAt 3066 1 32,
   opAt 3067 (.Swap ⟨0, by decide⟩),
   opAt 3068 .SUB,
   pushAt 3069 2 8224,
   opAt 3070 (.Dup ⟨1, by decide⟩),
   opAt 3071 .GT,
   pushAt 3072 2 4591,
   opAt 3073 .JUMPI]

/-- Fused selection and return, instructions 3155..3177, pc 4655..4685. -/
def blk3156 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3074 (.Dup ⟨1, by decide⟩),
   pushAt 3075 2 8224,
   opAt 3076 .MSTORE,
   opAt 3077 (.Dup ⟨2, by decide⟩),
   opAt 3078 .ISZERO,
   opAt 3079 (.Dup ⟨2, by decide⟩),
   opAt 3080 .OR,
   pushAt 3081 2 1088,
   opAt 3082 .MUL,
   pushAt 3083 2 8256,
   opAt 3084 .SUB,
   pushAt 3085 2 9344,
   opAt 3086 .MLOAD,
   opAt 3087 (.Swap ⟨0, by decide⟩),
   opAt 3088 (.Dup ⟨7, by decide⟩),
   opAt 3089 .MCOPY,
   opAt 3090 .POP,
   opAt 3091 .POP,
   opAt 3092 .POP,
   opAt 3093 .POP,
   opAt 3094 .POP,
   opAt 3095 .POP,
   opAt 3096 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
