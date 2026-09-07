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
  [opAt 2824 .JUMPDEST,
   opAt 2825 (.Dup ⟨0, by decide⟩),
   opAt 2826 .MLOAD,
   opAt 2827 .NOT,
   opAt 2828 (.Dup ⟨2, by decide⟩),
   opAt 2829 .ADD,
   opAt 2830 (.Dup ⟨2, by decide⟩),
   opAt 2831 (.Dup ⟨1, by decide⟩),
   opAt 2832 .LT,
   opAt 2833 (.Swap ⟨2, by decide⟩),
   opAt 2834 .POP,
   opAt 2835 (.Dup ⟨1, by decide⟩),
   pushAt 2836 2 5120,
   opAt 2837 .ADD,
   opAt 2838 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2839 (.Dup ⟨0, by decide⟩),
   opAt 2840 .ISZERO,
   pushAt 2841 2 4760,
   opAt 2842 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3005 .JUMPDEST,
   opAt 3006 (.Dup ⟨3, by decide⟩),
   opAt 3007 (.Dup ⟨1, by decide⟩),
   opAt 3008 .MLOAD,
   opAt 3009 (.Dup ⟨1, by decide⟩),
   opAt 3010 (.Dup ⟨1, by decide⟩),
   opAt 3011 .MUL,
   opAt 3012 (.Swap ⟨1, by decide⟩),
   pushAt 3013 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3014 (.Swap ⟨1, by decide⟩),
   opAt 3015 .MULMOD,
   opAt 3016 (.Dup ⟨1, by decide⟩),
   opAt 3017 (.Dup ⟨1, by decide⟩),
   opAt 3018 .LT,
   opAt 3019 (.Dup ⟨2, by decide⟩),
   opAt 3020 .ADD,
   opAt 3021 (.Swap ⟨0, by decide⟩),
   opAt 3022 .SUB,
   opAt 3023 (.Dup ⟨3, by decide⟩),
   opAt 3024 .MLOAD,
   opAt 3025 (.Swap ⟨1, by decide⟩),
   opAt 3026 (.Dup ⟨2, by decide⟩),
   opAt 3027 .ADD,
   opAt 3028 (.Swap ⟨1, by decide⟩),
   opAt 3029 (.Dup ⟨2, by decide⟩),
   opAt 3030 .LT,
   opAt 3031 .ADD,
   opAt 3032 (.Swap ⟨0, by decide⟩),
   opAt 3033 (.Dup ⟨4, by decide⟩),
   opAt 3034 .ADD,
   opAt 3035 (.Swap ⟨3, by decide⟩),
   opAt 3036 (.Dup ⟨4, by decide⟩),
   opAt 3037 .LT,
   opAt 3038 .ADD,
   opAt 3039 (.Swap ⟨2, by decide⟩),
   opAt 3040 (.Dup ⟨2, by decide⟩),
   opAt 3041 .MSTORE,
   pushAt 3042 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3043 .ADD,
   opAt 3044 (.Swap ⟨0, by decide⟩),
   pushAt 3045 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3046 .ADD,
   opAt 3047 (.Swap ⟨0, by decide⟩)]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3048 2 8224,
   opAt 3049 (.Dup ⟨2, by decide⟩),
   opAt 3050 .GT,
   pushAt 3051 2 4968,
   opAt 3052 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3085 .JUMPDEST,
   opAt 3086 (.Dup ⟨0, by decide⟩),
   opAt 3087 .MLOAD,
   opAt 3088 (.Dup ⟨1, by decide⟩),
   pushAt 3089 2 8256,
   opAt 3090 (.Swap ⟨0, by decide⟩),
   opAt 3091 .SUB,
   opAt 3092 .MLOAD,
   opAt 3093 (.Dup ⟨1, by decide⟩),
   opAt 3094 .ADD,
   opAt 3095 (.Dup ⟨0, by decide⟩),
   opAt 3096 (.Dup ⟨2, by decide⟩),
   opAt 3097 .GT,
   opAt 3098 (.Swap ⟨1, by decide⟩),
   opAt 3099 .POP,
   opAt 3100 (.Dup ⟨3, by decide⟩),
   opAt 3101 .ADD,
   opAt 3102 (.Dup ⟨0, by decide⟩),
   opAt 3103 (.Dup ⟨4, by decide⟩),
   opAt 3104 .GT,
   opAt 3105 (.Swap ⟨3, by decide⟩),
   opAt 3106 .POP,
   opAt 3107 (.Dup ⟨2, by decide⟩),
   opAt 3108 .MSTORE,
   opAt 3109 (.Swap ⟨0, by decide⟩),
   opAt 3110 (.Swap ⟨1, by decide⟩),
   opAt 3111 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3112 (.Swap ⟨0, by decide⟩),
   pushAt 3113 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3114 .ADD,
   pushAt 3115 2 8255,
   opAt 3116 (.Dup ⟨1, by decide⟩),
   opAt 3117 .GT,
   pushAt 3118 2 5156,
   opAt 3119 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3141 .JUMPDEST,
   opAt 3142 (.Dup ⟨0, by decide⟩),
   opAt 3143 .MLOAD,
   opAt 3144 (.Dup ⟨1, by decide⟩),
   pushAt 3145 2 8256,
   opAt 3146 (.Swap ⟨0, by decide⟩),
   opAt 3147 .SUB,
   opAt 3148 .MLOAD,
   opAt 3149 (.Dup ⟨1, by decide⟩),
   opAt 3150 (.Dup ⟨1, by decide⟩),
   opAt 3151 .GT,
   opAt 3152 (.Swap ⟨1, by decide⟩),
   opAt 3153 .SUB,
   opAt 3154 (.Dup ⟨3, by decide⟩),
   opAt 3155 (.Dup ⟨1, by decide⟩),
   opAt 3156 .LT,
   opAt 3157 (.Swap ⟨0, by decide⟩),
   opAt 3158 (.Dup ⟨4, by decide⟩),
   opAt 3159 (.Swap ⟨0, by decide⟩),
   opAt 3160 .SUB,
   opAt 3161 (.Dup ⟨3, by decide⟩),
   opAt 3162 .MSTORE,
   opAt 3163 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3164 (.Swap ⟨1, by decide⟩),
   opAt 3165 .POP,
   pushAt 3166 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3167 .ADD,
   pushAt 3168 2 8255,
   opAt 3169 (.Dup ⟨1, by decide⟩),
   opAt 3170 .GT,
   pushAt 3171 2 5262,
   opAt 3172 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
