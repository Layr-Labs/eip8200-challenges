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
  [opAt 2789 .JUMPDEST,
   opAt 2790 (.Dup ⟨0, by decide⟩),
   opAt 2791 .MLOAD,
   opAt 2792 .NOT,
   opAt 2793 (.Dup ⟨2, by decide⟩),
   opAt 2794 .ADD,
   opAt 2795 (.Dup ⟨2, by decide⟩),
   opAt 2796 (.Dup ⟨1, by decide⟩),
   opAt 2797 .LT,
   opAt 2798 (.Swap ⟨2, by decide⟩),
   opAt 2799 .POP,
   opAt 2800 (.Dup ⟨1, by decide⟩),
   pushAt 2801 2 5120,
   opAt 2802 .ADD,
   opAt 2803 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2804 (.Dup ⟨0, by decide⟩),
   opAt 2805 .ISZERO,
   pushAt 2806 2 3882,
   opAt 2807 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2972 .JUMPDEST,
   opAt 2973 (.Dup ⟨0, by decide⟩),
   opAt 2974 .MLOAD,
   pushAt 2975 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2976 (.Dup ⟨5, by decide⟩),
   opAt 2977 (.Dup ⟨2, by decide⟩),
   opAt 2978 .MUL,
   opAt 2979 (.Swap ⟨1, by decide⟩),
   opAt 2980 (.Dup ⟨6, by decide⟩),
   opAt 2981 .MULMOD,
   opAt 2982 (.Dup ⟨1, by decide⟩),
   opAt 2983 (.Dup ⟨1, by decide⟩),
   opAt 2984 .LT,
   opAt 2985 .SUB,
   opAt 2986 (.Dup ⟨4, by decide⟩),
   opAt 2987 (.Dup ⟨2, by decide⟩),
   opAt 2988 .ADD,
   opAt 2989 (.Dup ⟨0, by decide⟩),
   opAt 2990 (.Swap ⟨5, by decide⟩),
   opAt 2991 .GT,
   opAt 2992 .SUB,
   opAt 2993 .SUB,
   opAt 2994 (.Dup ⟨3, by decide⟩),
   opAt 2995 (.Dup ⟨3, by decide⟩),
   opAt 2996 .MLOAD,
   opAt 2997 .ADD,
   opAt 2998 (.Dup ⟨0, by decide⟩),
   opAt 2999 (.Swap ⟨4, by decide⟩),
   opAt 3000 .GT,
   opAt 3001 .ADD,
   opAt 3002 (.Swap ⟨2, by decide⟩),
   opAt 3003 (.Dup ⟨2, by decide⟩),
   pushAt 3004 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3005 .ADD,
   opAt 3006 (.Swap ⟨2, by decide⟩),
   opAt 3007 .MSTORE,
   pushAt 3008 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3009 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3010 2 8224,
   opAt 3011 (.Dup ⟨2, by decide⟩),
   opAt 3012 .GT,
   pushAt 3013 2 4093,
   opAt 3014 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3047 .JUMPDEST,
   opAt 3048 (.Dup ⟨0, by decide⟩),
   opAt 3049 .MLOAD,
   opAt 3050 (.Dup ⟨1, by decide⟩),
   pushAt 3051 2 8256,
   opAt 3052 (.Swap ⟨0, by decide⟩),
   opAt 3053 .SUB,
   opAt 3054 .MLOAD,
   opAt 3055 (.Dup ⟨1, by decide⟩),
   opAt 3056 .ADD,
   opAt 3057 (.Dup ⟨0, by decide⟩),
   opAt 3058 (.Dup ⟨2, by decide⟩),
   opAt 3059 .GT,
   opAt 3060 (.Swap ⟨1, by decide⟩),
   opAt 3061 .POP,
   opAt 3062 (.Dup ⟨3, by decide⟩),
   opAt 3063 .ADD,
   opAt 3064 (.Dup ⟨0, by decide⟩),
   opAt 3065 (.Dup ⟨4, by decide⟩),
   opAt 3066 .GT,
   opAt 3067 (.Swap ⟨3, by decide⟩),
   opAt 3068 .POP,
   opAt 3069 (.Dup ⟨2, by decide⟩),
   opAt 3070 .MSTORE,
   opAt 3071 (.Swap ⟨0, by decide⟩),
   opAt 3072 (.Swap ⟨1, by decide⟩),
   opAt 3073 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3074 (.Swap ⟨0, by decide⟩),
   pushAt 3075 1 31, opAt 3076 .NOT,
   opAt 3077 .ADD,
   pushAt 3078 2 8255,
   opAt 3079 (.Dup ⟨1, by decide⟩),
   opAt 3080 .GT,
   pushAt 3081 2 4276,
   opAt 3082 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3104 .JUMPDEST,
   opAt 3105 (.Dup ⟨0, by decide⟩),
   opAt 3106 .MLOAD,
   opAt 3107 (.Dup ⟨1, by decide⟩),
   pushAt 3108 2 8256,
   opAt 3109 (.Swap ⟨0, by decide⟩),
   opAt 3110 .SUB,
   opAt 3111 .MLOAD,
   opAt 3112 (.Dup ⟨1, by decide⟩),
   opAt 3113 (.Dup ⟨1, by decide⟩),
   opAt 3114 .GT,
   opAt 3115 (.Swap ⟨1, by decide⟩),
   opAt 3116 .SUB,
   opAt 3117 (.Dup ⟨3, by decide⟩),
   opAt 3118 (.Dup ⟨1, by decide⟩),
   opAt 3119 .LT,
   opAt 3120 (.Swap ⟨0, by decide⟩),
   opAt 3121 (.Dup ⟨4, by decide⟩),
   opAt 3122 (.Swap ⟨0, by decide⟩),
   opAt 3123 .SUB,
   opAt 3124 (.Dup ⟨3, by decide⟩),
   opAt 3125 .MSTORE,
   opAt 3126 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3127 (.Swap ⟨1, by decide⟩),
   opAt 3128 .POP,
   pushAt 3129 1 31, opAt 3130 .NOT,
   opAt 3131 .ADD,
   pushAt 3132 2 8255,
   opAt 3133 (.Dup ⟨1, by decide⟩),
   opAt 3134 .GT,
   pushAt 3135 2 4352,
   opAt 3136 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
