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
  [opAt 2791 .JUMPDEST,
   opAt 2792 (.Dup ⟨0, by decide⟩),
   opAt 2793 .MLOAD,
   opAt 2794 .NOT,
   opAt 2795 (.Dup ⟨2, by decide⟩),
   opAt 2796 .ADD,
   opAt 2797 (.Dup ⟨2, by decide⟩),
   opAt 2798 (.Dup ⟨1, by decide⟩),
   opAt 2799 .LT,
   opAt 2800 (.Swap ⟨2, by decide⟩),
   opAt 2801 .POP,
   opAt 2802 (.Dup ⟨1, by decide⟩),
   pushAt 2803 2 5120,
   opAt 2804 .ADD,
   opAt 2805 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2806 (.Dup ⟨0, by decide⟩),
   opAt 2807 .ISZERO,
   pushAt 2808 2 3932,
   opAt 2809 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2979 .JUMPDEST,
   opAt 2980 (.Dup ⟨0, by decide⟩),
   opAt 2981 .MLOAD,
   pushAt 2982 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2983 (.Dup ⟨5, by decide⟩),
   opAt 2984 (.Dup ⟨2, by decide⟩),
   opAt 2985 .MUL,
   opAt 2986 (.Swap ⟨1, by decide⟩),
   opAt 2987 (.Dup ⟨6, by decide⟩),
   opAt 2988 .MULMOD,
   opAt 2989 (.Dup ⟨1, by decide⟩),
   opAt 2990 (.Dup ⟨1, by decide⟩),
   opAt 2991 .LT,
   opAt 2992 .SUB,
   opAt 2993 (.Dup ⟨4, by decide⟩),
   opAt 2994 (.Dup ⟨2, by decide⟩),
   opAt 2995 .ADD,
   opAt 2996 (.Dup ⟨0, by decide⟩),
   opAt 2997 (.Swap ⟨5, by decide⟩),
   opAt 2998 .GT,
   opAt 2999 .SUB,
   opAt 3000 .SUB,
   opAt 3001 (.Dup ⟨3, by decide⟩),
   opAt 3002 (.Dup ⟨3, by decide⟩),
   opAt 3003 .MLOAD,
   opAt 3004 .ADD,
   opAt 3005 (.Dup ⟨0, by decide⟩),
   opAt 3006 (.Swap ⟨4, by decide⟩),
   opAt 3007 .GT,
   opAt 3008 .ADD,
   opAt 3009 (.Swap ⟨2, by decide⟩),
   opAt 3010 (.Dup ⟨2, by decide⟩),
   pushAt 3011 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3012 .ADD,
   opAt 3013 (.Swap ⟨2, by decide⟩),
   opAt 3014 .MSTORE,
   pushAt 3015 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3016 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3017 2 8224,
   opAt 3018 (.Dup ⟨2, by decide⟩),
   opAt 3019 .GT,
   pushAt 3020 2 4154,
   opAt 3021 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3054 .JUMPDEST,
   opAt 3055 (.Dup ⟨0, by decide⟩),
   opAt 3056 .MLOAD,
   opAt 3057 (.Dup ⟨1, by decide⟩),
   pushAt 3058 2 8256,
   opAt 3059 (.Swap ⟨0, by decide⟩),
   opAt 3060 .SUB,
   opAt 3061 .MLOAD,
   opAt 3062 (.Dup ⟨1, by decide⟩),
   opAt 3063 .ADD,
   opAt 3064 (.Dup ⟨0, by decide⟩),
   opAt 3065 (.Dup ⟨2, by decide⟩),
   opAt 3066 .GT,
   opAt 3067 (.Swap ⟨1, by decide⟩),
   opAt 3068 .POP,
   opAt 3069 (.Dup ⟨3, by decide⟩),
   opAt 3070 .ADD,
   opAt 3071 (.Dup ⟨0, by decide⟩),
   opAt 3072 (.Dup ⟨4, by decide⟩),
   opAt 3073 .GT,
   opAt 3074 (.Swap ⟨3, by decide⟩),
   opAt 3075 .POP,
   opAt 3076 (.Dup ⟨2, by decide⟩),
   opAt 3077 .MSTORE,
   opAt 3078 (.Swap ⟨0, by decide⟩),
   opAt 3079 (.Swap ⟨1, by decide⟩),
   opAt 3080 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3081 (.Swap ⟨0, by decide⟩),
   pushAt 3082 1 31,
   opAt 3083 .NOT,
   opAt 3084 .ADD,
   pushAt 3085 2 8255,
   opAt 3086 (.Dup ⟨1, by decide⟩),
   opAt 3087 .GT,
   pushAt 3088 2 4337,
   opAt 3089 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3111 .JUMPDEST,
   opAt 3112 (.Dup ⟨0, by decide⟩),
   opAt 3113 .MLOAD,
   opAt 3114 (.Dup ⟨1, by decide⟩),
   pushAt 3115 2 8256,
   opAt 3116 (.Swap ⟨0, by decide⟩),
   opAt 3117 .SUB,
   opAt 3118 .MLOAD,
   opAt 3119 (.Dup ⟨1, by decide⟩),
   opAt 3120 (.Dup ⟨1, by decide⟩),
   opAt 3121 .GT,
   opAt 3122 (.Swap ⟨1, by decide⟩),
   opAt 3123 .SUB,
   opAt 3124 (.Dup ⟨3, by decide⟩),
   opAt 3125 (.Dup ⟨1, by decide⟩),
   opAt 3126 .LT,
   opAt 3127 (.Swap ⟨0, by decide⟩),
   opAt 3128 (.Dup ⟨4, by decide⟩),
   opAt 3129 (.Swap ⟨0, by decide⟩),
   opAt 3130 .SUB,
   opAt 3131 (.Dup ⟨3, by decide⟩),
   opAt 3132 .MSTORE,
   opAt 3133 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3134 (.Swap ⟨1, by decide⟩),
   opAt 3135 .POP,
   pushAt 3136 1 31,
   opAt 3137 .NOT,
   opAt 3138 .ADD,
   pushAt 3139 2 8255,
   opAt 3140 (.Dup ⟨1, by decide⟩),
   opAt 3141 .GT,
   pushAt 3142 2 4413,
   opAt 3143 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
