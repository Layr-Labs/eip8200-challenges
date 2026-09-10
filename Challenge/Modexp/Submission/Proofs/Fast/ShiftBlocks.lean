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
  [opAt 2782 .JUMPDEST,
   opAt 2783 (.Dup ⟨0, by decide⟩),
   opAt 2784 .MLOAD,
   opAt 2785 .NOT,
   opAt 2786 (.Dup ⟨2, by decide⟩),
   opAt 2787 .ADD,
   opAt 2788 (.Dup ⟨2, by decide⟩),
   opAt 2789 (.Dup ⟨1, by decide⟩),
   opAt 2790 .LT,
   opAt 2791 (.Swap ⟨2, by decide⟩),
   opAt 2792 .POP,
   opAt 2793 (.Dup ⟨1, by decide⟩),
   pushAt 2794 2 5120,
   opAt 2795 .ADD,
   opAt 2796 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2797 (.Dup ⟨0, by decide⟩),
   opAt 2798 .ISZERO,
   pushAt 2799 2 3903,
   opAt 2800 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2971 .JUMPDEST,
   opAt 2972 (.Dup ⟨0, by decide⟩),
   opAt 2973 .MLOAD,
   pushAt 2974 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2975 (.Dup ⟨5, by decide⟩),
   opAt 2976 (.Dup ⟨2, by decide⟩),
   opAt 2977 .MUL,
   opAt 2978 (.Swap ⟨1, by decide⟩),
   opAt 2979 (.Dup ⟨6, by decide⟩),
   opAt 2980 .MULMOD,
   opAt 2981 (.Dup ⟨1, by decide⟩),
   opAt 2982 (.Dup ⟨1, by decide⟩),
   opAt 2983 .LT,
   opAt 2984 .SUB,
   opAt 2985 (.Dup ⟨4, by decide⟩),
   opAt 2986 (.Dup ⟨2, by decide⟩),
   opAt 2987 .ADD,
   opAt 2988 (.Dup ⟨0, by decide⟩),
   opAt 2989 (.Swap ⟨5, by decide⟩),
   opAt 2990 .GT,
   opAt 2991 .SUB,
   opAt 2992 .SUB,
   opAt 2993 (.Dup ⟨3, by decide⟩),
   opAt 2994 (.Dup ⟨3, by decide⟩),
   opAt 2995 .MLOAD,
   opAt 2996 .ADD,
   opAt 2997 (.Dup ⟨0, by decide⟩),
   opAt 2998 (.Swap ⟨4, by decide⟩),
   opAt 2999 .GT,
   opAt 3000 .ADD,
   opAt 3001 (.Swap ⟨2, by decide⟩),
   opAt 3002 (.Dup ⟨2, by decide⟩),
   pushAt 3003 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3004 .ADD,
   opAt 3005 (.Swap ⟨2, by decide⟩),
   opAt 3006 .MSTORE,
   pushAt 3007 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3008 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3009 2 8224,
   opAt 3010 (.Dup ⟨2, by decide⟩),
   opAt 3011 .GT,
   pushAt 3012 2 4126,
   opAt 3013 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3046 .JUMPDEST,
   opAt 3047 (.Dup ⟨0, by decide⟩),
   opAt 3048 .MLOAD,
   opAt 3049 (.Dup ⟨1, by decide⟩),
   pushAt 3050 2 8256,
   opAt 3051 (.Swap ⟨0, by decide⟩),
   opAt 3052 .SUB,
   opAt 3053 .MLOAD,
   opAt 3054 (.Dup ⟨1, by decide⟩),
   opAt 3055 .ADD,
   opAt 3056 (.Dup ⟨0, by decide⟩),
   opAt 3057 (.Dup ⟨2, by decide⟩),
   opAt 3058 .GT,
   opAt 3059 (.Swap ⟨1, by decide⟩),
   opAt 3060 .POP,
   opAt 3061 (.Dup ⟨3, by decide⟩),
   opAt 3062 .ADD,
   opAt 3063 (.Dup ⟨0, by decide⟩),
   opAt 3064 (.Dup ⟨4, by decide⟩),
   opAt 3065 .GT,
   opAt 3066 (.Swap ⟨3, by decide⟩),
   opAt 3067 .POP,
   opAt 3068 (.Dup ⟨2, by decide⟩),
   opAt 3069 .MSTORE,
   opAt 3070 (.Swap ⟨0, by decide⟩),
   opAt 3071 (.Swap ⟨1, by decide⟩),
   opAt 3072 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3073 (.Swap ⟨0, by decide⟩),
   pushAt 3074 1 31, opAt 3075 .NOT,
   opAt 3076 .ADD,
   pushAt 3077 2 8255,
   opAt 3078 (.Dup ⟨1, by decide⟩),
   opAt 3079 .GT,
   pushAt 3080 2 4309,
   opAt 3081 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3103 .JUMPDEST,
   opAt 3104 (.Dup ⟨0, by decide⟩),
   opAt 3105 .MLOAD,
   opAt 3106 (.Dup ⟨1, by decide⟩),
   pushAt 3107 2 8256,
   opAt 3108 (.Swap ⟨0, by decide⟩),
   opAt 3109 .SUB,
   opAt 3110 .MLOAD,
   opAt 3111 (.Dup ⟨1, by decide⟩),
   opAt 3112 (.Dup ⟨1, by decide⟩),
   opAt 3113 .GT,
   opAt 3114 (.Swap ⟨1, by decide⟩),
   opAt 3115 .SUB,
   opAt 3116 (.Dup ⟨3, by decide⟩),
   opAt 3117 (.Dup ⟨1, by decide⟩),
   opAt 3118 .LT,
   opAt 3119 (.Swap ⟨0, by decide⟩),
   opAt 3120 (.Dup ⟨4, by decide⟩),
   opAt 3121 (.Swap ⟨0, by decide⟩),
   opAt 3122 .SUB,
   opAt 3123 (.Dup ⟨3, by decide⟩),
   opAt 3124 .MSTORE,
   opAt 3125 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3126 (.Swap ⟨1, by decide⟩),
   opAt 3127 .POP,
   pushAt 3128 1 31, opAt 3129 .NOT,
   opAt 3130 .ADD,
   pushAt 3131 2 8255,
   opAt 3132 (.Dup ⟨1, by decide⟩),
   opAt 3133 .GT,
   pushAt 3134 2 4385,
   opAt 3135 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
