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
  [opAt 2896 .JUMPDEST,
   opAt 2897 (.Dup ⟨0, by decide⟩),
   opAt 2898 .MLOAD,
   opAt 2899 .NOT,
   opAt 2900 (.Dup ⟨2, by decide⟩),
   opAt 2901 .ADD,
   opAt 2902 (.Dup ⟨2, by decide⟩),
   opAt 2903 (.Dup ⟨1, by decide⟩),
   opAt 2904 .LT,
   opAt 2905 (.Swap ⟨2, by decide⟩),
   opAt 2906 .POP,
   opAt 2907 (.Dup ⟨1, by decide⟩),
   pushAt 2908 2 5120,
   opAt 2909 .ADD,
   opAt 2910 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2911 (.Dup ⟨0, by decide⟩),
   opAt 2912 .ISZERO,
   pushAt 2913 2 4760,
   opAt 2914 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3077 .JUMPDEST,
   opAt 3078 (.Dup ⟨3, by decide⟩),
   opAt 3079 (.Dup ⟨1, by decide⟩),
   opAt 3080 .MLOAD,
   opAt 3081 (.Dup ⟨1, by decide⟩),
   opAt 3082 (.Dup ⟨1, by decide⟩),
   opAt 3083 .MUL,
   opAt 3084 (.Swap ⟨1, by decide⟩),
   pushAt 3085 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3086 (.Swap ⟨1, by decide⟩),
   opAt 3087 .MULMOD,
   opAt 3088 (.Dup ⟨1, by decide⟩),
   opAt 3089 (.Dup ⟨1, by decide⟩),
   opAt 3090 .LT,
   opAt 3091 (.Dup ⟨2, by decide⟩),
   opAt 3092 .ADD,
   opAt 3093 (.Swap ⟨0, by decide⟩),
   opAt 3094 .SUB,
   opAt 3095 (.Dup ⟨3, by decide⟩),
   opAt 3096 .MLOAD,
   opAt 3097 (.Swap ⟨1, by decide⟩),
   opAt 3098 (.Dup ⟨2, by decide⟩),
   opAt 3099 .ADD,
   opAt 3100 (.Swap ⟨1, by decide⟩),
   opAt 3101 (.Dup ⟨2, by decide⟩),
   opAt 3102 .LT,
   opAt 3103 .ADD,
   opAt 3104 (.Swap ⟨0, by decide⟩),
   opAt 3105 (.Dup ⟨4, by decide⟩),
   opAt 3106 .ADD,
   opAt 3107 (.Swap ⟨3, by decide⟩),
   opAt 3108 (.Dup ⟨4, by decide⟩),
   opAt 3109 .LT,
   opAt 3110 .ADD,
   opAt 3111 (.Swap ⟨2, by decide⟩),
   opAt 3112 (.Dup ⟨2, by decide⟩),
   opAt 3113 .MSTORE,
   pushAt 3114 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3115 .ADD,
   opAt 3116 (.Swap ⟨0, by decide⟩),
   pushAt 3117 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3118 .ADD,
   opAt 3119 (.Swap ⟨0, by decide⟩)]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3120 2 8224,
   opAt 3121 (.Dup ⟨2, by decide⟩),
   opAt 3122 .GT,
   pushAt 3123 2 4968,
   opAt 3124 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3157 .JUMPDEST,
   opAt 3158 (.Dup ⟨0, by decide⟩),
   opAt 3159 .MLOAD,
   opAt 3160 (.Dup ⟨1, by decide⟩),
   pushAt 3161 2 8256,
   opAt 3162 (.Swap ⟨0, by decide⟩),
   opAt 3163 .SUB,
   opAt 3164 .MLOAD,
   opAt 3165 (.Dup ⟨1, by decide⟩),
   opAt 3166 .ADD,
   opAt 3167 (.Dup ⟨0, by decide⟩),
   opAt 3168 (.Dup ⟨2, by decide⟩),
   opAt 3169 .GT,
   opAt 3170 (.Swap ⟨1, by decide⟩),
   opAt 3171 .POP,
   opAt 3172 (.Dup ⟨3, by decide⟩),
   opAt 3173 .ADD,
   opAt 3174 (.Dup ⟨0, by decide⟩),
   opAt 3175 (.Dup ⟨4, by decide⟩),
   opAt 3176 .GT,
   opAt 3177 (.Swap ⟨3, by decide⟩),
   opAt 3178 .POP,
   opAt 3179 (.Dup ⟨2, by decide⟩),
   opAt 3180 .MSTORE,
   opAt 3181 (.Swap ⟨0, by decide⟩),
   opAt 3182 (.Swap ⟨1, by decide⟩),
   opAt 3183 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3184 (.Swap ⟨0, by decide⟩),
   pushAt 3185 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3186 .ADD,
   pushAt 3187 2 8255,
   opAt 3188 (.Dup ⟨1, by decide⟩),
   opAt 3189 .GT,
   pushAt 3190 2 5156,
   opAt 3191 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3213 .JUMPDEST,
   opAt 3214 (.Dup ⟨0, by decide⟩),
   opAt 3215 .MLOAD,
   opAt 3216 (.Dup ⟨1, by decide⟩),
   pushAt 3217 2 8256,
   opAt 3218 (.Swap ⟨0, by decide⟩),
   opAt 3219 .SUB,
   opAt 3220 .MLOAD,
   opAt 3221 (.Dup ⟨1, by decide⟩),
   opAt 3222 (.Dup ⟨1, by decide⟩),
   opAt 3223 .GT,
   opAt 3224 (.Swap ⟨1, by decide⟩),
   opAt 3225 .SUB,
   opAt 3226 (.Dup ⟨3, by decide⟩),
   opAt 3227 (.Dup ⟨1, by decide⟩),
   opAt 3228 .LT,
   opAt 3229 (.Swap ⟨0, by decide⟩),
   opAt 3230 (.Dup ⟨4, by decide⟩),
   opAt 3231 (.Swap ⟨0, by decide⟩),
   opAt 3232 .SUB,
   opAt 3233 (.Dup ⟨3, by decide⟩),
   opAt 3234 .MSTORE,
   opAt 3235 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3236 (.Swap ⟨1, by decide⟩),
   opAt 3237 .POP,
   pushAt 3238 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3239 .ADD,
   pushAt 3240 2 8255,
   opAt 3241 (.Dup ⟨1, by decide⟩),
   opAt 3242 .GT,
   pushAt 3243 2 5262,
   opAt 3244 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
