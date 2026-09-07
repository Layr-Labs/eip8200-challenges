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
  [opAt 2814 .JUMPDEST,
   opAt 2815 (.Dup ⟨0, by decide⟩),
   opAt 2816 .MLOAD,
   opAt 2817 .NOT,
   opAt 2818 (.Dup ⟨2, by decide⟩),
   opAt 2819 .ADD,
   opAt 2820 (.Dup ⟨2, by decide⟩),
   opAt 2821 (.Dup ⟨1, by decide⟩),
   opAt 2822 .LT,
   opAt 2823 (.Swap ⟨2, by decide⟩),
   opAt 2824 .POP,
   opAt 2825 (.Dup ⟨1, by decide⟩),
   pushAt 2826 2 5120,
   opAt 2827 .ADD,
   opAt 2828 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2829 (.Dup ⟨0, by decide⟩),
   opAt 2830 .ISZERO,
   pushAt 2831 2 4760,
   opAt 2832 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2995 .JUMPDEST,
   opAt 2996 (.Dup ⟨3, by decide⟩),
   opAt 2997 (.Dup ⟨1, by decide⟩),
   opAt 2998 .MLOAD,
   opAt 2999 (.Dup ⟨1, by decide⟩),
   opAt 3000 (.Dup ⟨1, by decide⟩),
   opAt 3001 .MUL,
   opAt 3002 (.Swap ⟨1, by decide⟩),
   pushAt 3003 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3004 (.Swap ⟨1, by decide⟩),
   opAt 3005 .MULMOD,
   opAt 3006 (.Dup ⟨1, by decide⟩),
   opAt 3007 (.Dup ⟨1, by decide⟩),
   opAt 3008 .LT,
   opAt 3009 (.Dup ⟨2, by decide⟩),
   opAt 3010 .ADD,
   opAt 3011 (.Swap ⟨0, by decide⟩),
   opAt 3012 .SUB,
   opAt 3013 (.Dup ⟨3, by decide⟩),
   opAt 3014 .MLOAD,
   opAt 3015 (.Swap ⟨1, by decide⟩),
   opAt 3016 (.Dup ⟨2, by decide⟩),
   opAt 3017 .ADD,
   opAt 3018 (.Swap ⟨1, by decide⟩),
   opAt 3019 (.Dup ⟨2, by decide⟩),
   opAt 3020 .LT,
   opAt 3021 .ADD,
   opAt 3022 (.Swap ⟨0, by decide⟩),
   opAt 3023 (.Dup ⟨4, by decide⟩),
   opAt 3024 .ADD,
   opAt 3025 (.Swap ⟨3, by decide⟩),
   opAt 3026 (.Dup ⟨4, by decide⟩),
   opAt 3027 .LT,
   opAt 3028 .ADD,
   opAt 3029 (.Swap ⟨2, by decide⟩),
   opAt 3030 (.Dup ⟨2, by decide⟩),
   opAt 3031 .MSTORE,
   pushAt 3032 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3033 .ADD,
   opAt 3034 (.Swap ⟨0, by decide⟩),
   pushAt 3035 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3036 .ADD,
   opAt 3037 (.Swap ⟨0, by decide⟩)]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3038 2 8224,
   opAt 3039 (.Dup ⟨2, by decide⟩),
   opAt 3040 .GT,
   pushAt 3041 2 4968,
   opAt 3042 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3075 .JUMPDEST,
   opAt 3076 (.Dup ⟨0, by decide⟩),
   opAt 3077 .MLOAD,
   opAt 3078 (.Dup ⟨1, by decide⟩),
   pushAt 3079 2 8256,
   opAt 3080 (.Swap ⟨0, by decide⟩),
   opAt 3081 .SUB,
   opAt 3082 .MLOAD,
   opAt 3083 (.Dup ⟨1, by decide⟩),
   opAt 3084 .ADD,
   opAt 3085 (.Dup ⟨0, by decide⟩),
   opAt 3086 (.Dup ⟨2, by decide⟩),
   opAt 3087 .GT,
   opAt 3088 (.Swap ⟨1, by decide⟩),
   opAt 3089 .POP,
   opAt 3090 (.Dup ⟨3, by decide⟩),
   opAt 3091 .ADD,
   opAt 3092 (.Dup ⟨0, by decide⟩),
   opAt 3093 (.Dup ⟨4, by decide⟩),
   opAt 3094 .GT,
   opAt 3095 (.Swap ⟨3, by decide⟩),
   opAt 3096 .POP,
   opAt 3097 (.Dup ⟨2, by decide⟩),
   opAt 3098 .MSTORE,
   opAt 3099 (.Swap ⟨0, by decide⟩),
   opAt 3100 (.Swap ⟨1, by decide⟩),
   opAt 3101 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3102 (.Swap ⟨0, by decide⟩),
   pushAt 3103 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3104 .ADD,
   pushAt 3105 2 8255,
   opAt 3106 (.Dup ⟨1, by decide⟩),
   opAt 3107 .GT,
   pushAt 3108 2 5156,
   opAt 3109 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3131 .JUMPDEST,
   opAt 3132 (.Dup ⟨0, by decide⟩),
   opAt 3133 .MLOAD,
   opAt 3134 (.Dup ⟨1, by decide⟩),
   pushAt 3135 2 8256,
   opAt 3136 (.Swap ⟨0, by decide⟩),
   opAt 3137 .SUB,
   opAt 3138 .MLOAD,
   opAt 3139 (.Dup ⟨1, by decide⟩),
   opAt 3140 (.Dup ⟨1, by decide⟩),
   opAt 3141 .GT,
   opAt 3142 (.Swap ⟨1, by decide⟩),
   opAt 3143 .SUB,
   opAt 3144 (.Dup ⟨3, by decide⟩),
   opAt 3145 (.Dup ⟨1, by decide⟩),
   opAt 3146 .LT,
   opAt 3147 (.Swap ⟨0, by decide⟩),
   opAt 3148 (.Dup ⟨4, by decide⟩),
   opAt 3149 (.Swap ⟨0, by decide⟩),
   opAt 3150 .SUB,
   opAt 3151 (.Dup ⟨3, by decide⟩),
   opAt 3152 .MSTORE,
   opAt 3153 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3154 (.Swap ⟨1, by decide⟩),
   opAt 3155 .POP,
   pushAt 3156 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3157 .ADD,
   pushAt 3158 2 8255,
   opAt 3159 (.Dup ⟨1, by decide⟩),
   opAt 3160 .GT,
   pushAt 3161 2 5262,
   opAt 3162 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
