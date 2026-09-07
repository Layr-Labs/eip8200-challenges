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
  [opAt 2798 .JUMPDEST,
   opAt 2799 (.Dup ⟨0, by decide⟩),
   opAt 2800 .MLOAD,
   opAt 2801 .NOT,
   opAt 2802 (.Dup ⟨2, by decide⟩),
   opAt 2803 .ADD,
   opAt 2804 (.Dup ⟨2, by decide⟩),
   opAt 2805 (.Dup ⟨1, by decide⟩),
   opAt 2806 .LT,
   opAt 2807 (.Swap ⟨2, by decide⟩),
   opAt 2808 .POP,
   opAt 2809 (.Dup ⟨1, by decide⟩),
   pushAt 2810 2 5120,
   opAt 2811 .ADD,
   opAt 2812 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2813 (.Dup ⟨0, by decide⟩),
   opAt 2814 .ISZERO,
   pushAt 2815 2 4678,
   opAt 2816 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2979 .JUMPDEST,
   opAt 2980 (.Dup ⟨3, by decide⟩),
   opAt 2981 (.Dup ⟨1, by decide⟩),
   opAt 2982 .MLOAD,
   opAt 2983 (.Dup ⟨1, by decide⟩),
   opAt 2984 (.Dup ⟨1, by decide⟩),
   opAt 2985 .MUL,
   opAt 2986 (.Swap ⟨1, by decide⟩),
   pushAt 2987 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2988 (.Swap ⟨1, by decide⟩),
   opAt 2989 .MULMOD,
   opAt 2990 (.Dup ⟨1, by decide⟩),
   opAt 2991 (.Dup ⟨1, by decide⟩),
   opAt 2992 .LT,
   opAt 2993 (.Dup ⟨2, by decide⟩),
   opAt 2994 .ADD,
   opAt 2995 (.Swap ⟨0, by decide⟩),
   opAt 2996 .SUB,
   opAt 2997 (.Dup ⟨3, by decide⟩),
   opAt 2998 .MLOAD,
   opAt 2999 (.Swap ⟨1, by decide⟩),
   opAt 3000 (.Dup ⟨2, by decide⟩),
   opAt 3001 .ADD,
   opAt 3002 (.Swap ⟨1, by decide⟩),
   opAt 3003 (.Dup ⟨2, by decide⟩),
   opAt 3004 .LT,
   opAt 3005 .ADD,
   opAt 3006 (.Swap ⟨0, by decide⟩),
   opAt 3007 (.Dup ⟨4, by decide⟩),
   opAt 3008 .ADD,
   opAt 3009 (.Swap ⟨3, by decide⟩),
   opAt 3010 (.Dup ⟨4, by decide⟩),
   opAt 3011 .LT,
   opAt 3012 .ADD,
   opAt 3013 (.Swap ⟨2, by decide⟩),
   opAt 3014 (.Dup ⟨2, by decide⟩),
   opAt 3015 .MSTORE,
   pushAt 3016 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3017 .ADD,
   opAt 3018 (.Swap ⟨0, by decide⟩),
   pushAt 3019 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3020 .ADD,
   opAt 3021 (.Swap ⟨0, by decide⟩)]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3022 2 8224,
   opAt 3023 (.Dup ⟨2, by decide⟩),
   opAt 3024 .GT,
   pushAt 3025 2 4886,
   opAt 3026 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3059 .JUMPDEST,
   opAt 3060 (.Dup ⟨0, by decide⟩),
   opAt 3061 .MLOAD,
   opAt 3062 (.Dup ⟨1, by decide⟩),
   pushAt 3063 2 8256,
   opAt 3064 (.Swap ⟨0, by decide⟩),
   opAt 3065 .SUB,
   opAt 3066 .MLOAD,
   opAt 3067 (.Dup ⟨1, by decide⟩),
   opAt 3068 .ADD,
   opAt 3069 (.Dup ⟨0, by decide⟩),
   opAt 3070 (.Dup ⟨2, by decide⟩),
   opAt 3071 .GT,
   opAt 3072 (.Swap ⟨1, by decide⟩),
   opAt 3073 .POP,
   opAt 3074 (.Dup ⟨3, by decide⟩),
   opAt 3075 .ADD,
   opAt 3076 (.Dup ⟨0, by decide⟩),
   opAt 3077 (.Dup ⟨4, by decide⟩),
   opAt 3078 .GT,
   opAt 3079 (.Swap ⟨3, by decide⟩),
   opAt 3080 .POP,
   opAt 3081 (.Dup ⟨2, by decide⟩),
   opAt 3082 .MSTORE,
   opAt 3083 (.Swap ⟨0, by decide⟩),
   opAt 3084 (.Swap ⟨1, by decide⟩),
   opAt 3085 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3086 (.Swap ⟨0, by decide⟩),
   pushAt 3087 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3088 .ADD,
   pushAt 3089 2 8255,
   opAt 3090 (.Dup ⟨1, by decide⟩),
   opAt 3091 .GT,
   pushAt 3092 2 5074,
   opAt 3093 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3115 .JUMPDEST,
   opAt 3116 (.Dup ⟨0, by decide⟩),
   opAt 3117 .MLOAD,
   opAt 3118 (.Dup ⟨1, by decide⟩),
   pushAt 3119 2 8256,
   opAt 3120 (.Swap ⟨0, by decide⟩),
   opAt 3121 .SUB,
   opAt 3122 .MLOAD,
   opAt 3123 (.Dup ⟨1, by decide⟩),
   opAt 3124 (.Dup ⟨1, by decide⟩),
   opAt 3125 .GT,
   opAt 3126 (.Swap ⟨1, by decide⟩),
   opAt 3127 .SUB,
   opAt 3128 (.Dup ⟨3, by decide⟩),
   opAt 3129 (.Dup ⟨1, by decide⟩),
   opAt 3130 .LT,
   opAt 3131 (.Swap ⟨0, by decide⟩),
   opAt 3132 (.Dup ⟨4, by decide⟩),
   opAt 3133 (.Swap ⟨0, by decide⟩),
   opAt 3134 .SUB,
   opAt 3135 (.Dup ⟨3, by decide⟩),
   opAt 3136 .MSTORE,
   opAt 3137 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3138 (.Swap ⟨1, by decide⟩),
   opAt 3139 .POP,
   pushAt 3140 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3141 .ADD,
   pushAt 3142 2 8255,
   opAt 3143 (.Dup ⟨1, by decide⟩),
   opAt 3144 .GT,
   pushAt 3145 2 5180,
   opAt 3146 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
