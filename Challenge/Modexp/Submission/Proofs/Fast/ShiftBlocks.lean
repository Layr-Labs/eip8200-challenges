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
  [opAt 2974 .JUMPDEST,
   opAt 2975 (.Dup ⟨0, by decide⟩),
   opAt 2976 .MLOAD,
   pushAt 2977 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2978 (.Dup ⟨5, by decide⟩),
   opAt 2979 (.Dup ⟨2, by decide⟩),
   opAt 2980 .MUL,
   opAt 2981 (.Swap ⟨1, by decide⟩),
   opAt 2982 (.Dup ⟨6, by decide⟩),
   opAt 2983 .MULMOD,
   opAt 2984 (.Dup ⟨1, by decide⟩),
   opAt 2985 (.Dup ⟨1, by decide⟩),
   opAt 2986 .LT,
   opAt 2987 .SUB,
   opAt 2988 (.Dup ⟨4, by decide⟩),
   opAt 2989 (.Dup ⟨2, by decide⟩),
   opAt 2990 .ADD,
   opAt 2991 (.Dup ⟨0, by decide⟩),
   opAt 2992 (.Swap ⟨5, by decide⟩),
   opAt 2993 .GT,
   opAt 2994 .SUB,
   opAt 2995 .SUB,
   opAt 2996 (.Dup ⟨3, by decide⟩),
   opAt 2997 (.Dup ⟨3, by decide⟩),
   opAt 2998 .MLOAD,
   opAt 2999 .ADD,
   opAt 3000 (.Dup ⟨0, by decide⟩),
   opAt 3001 (.Swap ⟨4, by decide⟩),
   opAt 3002 .GT,
   opAt 3003 .ADD,
   opAt 3004 (.Swap ⟨2, by decide⟩),
   opAt 3005 (.Dup ⟨2, by decide⟩),
   pushAt 3006 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3007 .ADD,
   opAt 3008 (.Swap ⟨2, by decide⟩),
   opAt 3009 .MSTORE,
   pushAt 3010 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3011 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3012 2 8224,
   opAt 3013 (.Dup ⟨2, by decide⟩),
   opAt 3014 .GT,
   pushAt 3015 2 4119,
   opAt 3016 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3049 .JUMPDEST,
   opAt 3050 (.Dup ⟨0, by decide⟩),
   opAt 3051 .MLOAD,
   opAt 3052 (.Dup ⟨1, by decide⟩),
   pushAt 3053 2 8256,
   opAt 3054 (.Swap ⟨0, by decide⟩),
   opAt 3055 .SUB,
   opAt 3056 .MLOAD,
   opAt 3057 (.Dup ⟨1, by decide⟩),
   opAt 3058 .ADD,
   opAt 3059 (.Dup ⟨0, by decide⟩),
   opAt 3060 (.Dup ⟨2, by decide⟩),
   opAt 3061 .GT,
   opAt 3062 (.Swap ⟨1, by decide⟩),
   opAt 3063 .POP,
   opAt 3064 (.Dup ⟨3, by decide⟩),
   opAt 3065 .ADD,
   opAt 3066 (.Dup ⟨0, by decide⟩),
   opAt 3067 (.Dup ⟨4, by decide⟩),
   opAt 3068 .GT,
   opAt 3069 (.Swap ⟨3, by decide⟩),
   opAt 3070 .POP,
   opAt 3071 (.Dup ⟨2, by decide⟩),
   opAt 3072 .MSTORE,
   opAt 3073 (.Swap ⟨0, by decide⟩),
   opAt 3074 (.Swap ⟨1, by decide⟩),
   opAt 3075 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3076 (.Swap ⟨0, by decide⟩),
   pushAt 3077 1 31, opAt 3078 .NOT,
   opAt 3079 .ADD,
   pushAt 3080 2 8255,
   opAt 3081 (.Dup ⟨1, by decide⟩),
   opAt 3082 .GT,
   pushAt 3083 2 4302,
   opAt 3084 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3106 .JUMPDEST,
   opAt 3107 (.Dup ⟨0, by decide⟩),
   opAt 3108 .MLOAD,
   opAt 3109 (.Dup ⟨1, by decide⟩),
   pushAt 3110 2 8256,
   opAt 3111 (.Swap ⟨0, by decide⟩),
   opAt 3112 .SUB,
   opAt 3113 .MLOAD,
   opAt 3114 (.Dup ⟨1, by decide⟩),
   opAt 3115 (.Dup ⟨1, by decide⟩),
   opAt 3116 .GT,
   opAt 3117 (.Swap ⟨1, by decide⟩),
   opAt 3118 .SUB,
   opAt 3119 (.Dup ⟨3, by decide⟩),
   opAt 3120 (.Dup ⟨1, by decide⟩),
   opAt 3121 .LT,
   opAt 3122 (.Swap ⟨0, by decide⟩),
   opAt 3123 (.Dup ⟨4, by decide⟩),
   opAt 3124 (.Swap ⟨0, by decide⟩),
   opAt 3125 .SUB,
   opAt 3126 (.Dup ⟨3, by decide⟩),
   opAt 3127 .MSTORE,
   opAt 3128 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3129 (.Swap ⟨1, by decide⟩),
   opAt 3130 .POP,
   pushAt 3131 1 31, opAt 3132 .NOT,
   opAt 3133 .ADD,
   pushAt 3134 2 8255,
   opAt 3135 (.Dup ⟨1, by decide⟩),
   opAt 3136 .GT,
   pushAt 3137 2 4378,
   opAt 3138 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
