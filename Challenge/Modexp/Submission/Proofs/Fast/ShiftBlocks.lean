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
  [opAt 2790 .JUMPDEST,
   opAt 2791 (.Dup ⟨0, by decide⟩),
   opAt 2792 .MLOAD,
   opAt 2793 .NOT,
   opAt 2794 (.Dup ⟨2, by decide⟩),
   opAt 2795 .ADD,
   opAt 2796 (.Dup ⟨2, by decide⟩),
   opAt 2797 (.Dup ⟨1, by decide⟩),
   opAt 2798 .LT,
   opAt 2799 (.Swap ⟨2, by decide⟩),
   opAt 2800 .POP,
   opAt 2801 (.Dup ⟨1, by decide⟩),
   pushAt 2802 2 5120,
   opAt 2803 .ADD,
   opAt 2804 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2805 (.Dup ⟨0, by decide⟩),
   opAt 2806 .ISZERO,
   pushAt 2807 2 3903,
   opAt 2808 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2978 .JUMPDEST,
   opAt 2979 (.Dup ⟨0, by decide⟩),
   opAt 2980 .MLOAD,
   pushAt 2981 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2982 (.Dup ⟨5, by decide⟩),
   opAt 2983 (.Dup ⟨2, by decide⟩),
   opAt 2984 .MUL,
   opAt 2985 (.Swap ⟨1, by decide⟩),
   opAt 2986 (.Dup ⟨6, by decide⟩),
   opAt 2987 .MULMOD,
   opAt 2988 (.Dup ⟨1, by decide⟩),
   opAt 2989 (.Dup ⟨1, by decide⟩),
   opAt 2990 .LT,
   opAt 2991 .SUB,
   opAt 2992 (.Dup ⟨4, by decide⟩),
   opAt 2993 (.Dup ⟨2, by decide⟩),
   opAt 2994 .ADD,
   opAt 2995 (.Dup ⟨0, by decide⟩),
   opAt 2996 (.Swap ⟨5, by decide⟩),
   opAt 2997 .GT,
   opAt 2998 .SUB,
   opAt 2999 .SUB,
   opAt 3000 (.Dup ⟨3, by decide⟩),
   opAt 3001 (.Dup ⟨3, by decide⟩),
   opAt 3002 .MLOAD,
   opAt 3003 .ADD,
   opAt 3004 (.Dup ⟨0, by decide⟩),
   opAt 3005 (.Swap ⟨4, by decide⟩),
   opAt 3006 .GT,
   opAt 3007 .ADD,
   opAt 3008 (.Swap ⟨2, by decide⟩),
   opAt 3009 (.Dup ⟨2, by decide⟩),
   pushAt 3010 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3011 .ADD,
   opAt 3012 (.Swap ⟨2, by decide⟩),
   opAt 3013 .MSTORE,
   pushAt 3014 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3015 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3016 2 8224,
   opAt 3017 (.Dup ⟨2, by decide⟩),
   opAt 3018 .GT,
   pushAt 3019 2 4119,
   opAt 3020 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3053 .JUMPDEST,
   opAt 3054 (.Dup ⟨0, by decide⟩),
   opAt 3055 .MLOAD,
   opAt 3056 (.Dup ⟨1, by decide⟩),
   pushAt 3057 2 8256,
   opAt 3058 (.Swap ⟨0, by decide⟩),
   opAt 3059 .SUB,
   opAt 3060 .MLOAD,
   opAt 3061 (.Dup ⟨1, by decide⟩),
   opAt 3062 .ADD,
   opAt 3063 (.Dup ⟨0, by decide⟩),
   opAt 3064 (.Dup ⟨2, by decide⟩),
   opAt 3065 .GT,
   opAt 3066 (.Swap ⟨1, by decide⟩),
   opAt 3067 .POP,
   opAt 3068 (.Dup ⟨3, by decide⟩),
   opAt 3069 .ADD,
   opAt 3070 (.Dup ⟨0, by decide⟩),
   opAt 3071 (.Dup ⟨4, by decide⟩),
   opAt 3072 .GT,
   opAt 3073 (.Swap ⟨3, by decide⟩),
   opAt 3074 .POP,
   opAt 3075 (.Dup ⟨2, by decide⟩),
   opAt 3076 .MSTORE,
   opAt 3077 (.Swap ⟨0, by decide⟩),
   opAt 3078 (.Swap ⟨1, by decide⟩),
   opAt 3079 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3080 (.Swap ⟨0, by decide⟩),
   pushAt 3081 1 31, opAt 3082 .NOT,
   opAt 3083 .ADD,
   pushAt 3084 2 8255,
   opAt 3085 (.Dup ⟨1, by decide⟩),
   opAt 3086 .GT,
   pushAt 3087 2 4302,
   opAt 3088 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3110 .JUMPDEST,
   opAt 3111 (.Dup ⟨0, by decide⟩),
   opAt 3112 .MLOAD,
   opAt 3113 (.Dup ⟨1, by decide⟩),
   pushAt 3114 2 8256,
   opAt 3115 (.Swap ⟨0, by decide⟩),
   opAt 3116 .SUB,
   opAt 3117 .MLOAD,
   opAt 3118 (.Dup ⟨1, by decide⟩),
   opAt 3119 (.Dup ⟨1, by decide⟩),
   opAt 3120 .GT,
   opAt 3121 (.Swap ⟨1, by decide⟩),
   opAt 3122 .SUB,
   opAt 3123 (.Dup ⟨3, by decide⟩),
   opAt 3124 (.Dup ⟨1, by decide⟩),
   opAt 3125 .LT,
   opAt 3126 (.Swap ⟨0, by decide⟩),
   opAt 3127 (.Dup ⟨4, by decide⟩),
   opAt 3128 (.Swap ⟨0, by decide⟩),
   opAt 3129 .SUB,
   opAt 3130 (.Dup ⟨3, by decide⟩),
   opAt 3131 .MSTORE,
   opAt 3132 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3133 (.Swap ⟨1, by decide⟩),
   opAt 3134 .POP,
   pushAt 3135 1 31, opAt 3136 .NOT,
   opAt 3137 .ADD,
   pushAt 3138 2 8255,
   opAt 3139 (.Dup ⟨1, by decide⟩),
   opAt 3140 .GT,
   pushAt 3141 2 4378,
   opAt 3142 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
