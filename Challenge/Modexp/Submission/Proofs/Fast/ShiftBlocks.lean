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
  [opAt 2728 .JUMPDEST,
   opAt 2729 (.Dup ⟨0, by decide⟩),
   opAt 2730 .MLOAD,
   opAt 2731 .NOT,
   opAt 2732 (.Dup ⟨2, by decide⟩),
   opAt 2733 .ADD,
   opAt 2734 (.Dup ⟨2, by decide⟩),
   opAt 2735 (.Dup ⟨1, by decide⟩),
   opAt 2736 .LT,
   opAt 2737 (.Swap ⟨2, by decide⟩),
   opAt 2738 .POP,
   opAt 2739 (.Dup ⟨1, by decide⟩),
   pushAt 2740 2 5120,
   opAt 2741 .ADD,
   opAt 2742 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2743 (.Dup ⟨0, by decide⟩),
   opAt 2744 .ISZERO,
   pushAt 2745 2 4735,
   opAt 2746 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2916 .JUMPDEST,
   opAt 2917 (.Dup ⟨0, by decide⟩),
   opAt 2918 .MLOAD,
   pushAt 2919 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2920 (.Dup ⟨5, by decide⟩),
   opAt 2921 (.Dup ⟨2, by decide⟩),
   opAt 2922 .MUL,
   opAt 2923 (.Swap ⟨1, by decide⟩),
   opAt 2924 (.Dup ⟨6, by decide⟩),
   opAt 2925 .MULMOD,
   opAt 2926 (.Dup ⟨1, by decide⟩),
   opAt 2927 (.Dup ⟨1, by decide⟩),
   opAt 2928 .LT,
   opAt 2929 .SUB,
   opAt 2930 (.Dup ⟨4, by decide⟩),
   opAt 2931 (.Dup ⟨2, by decide⟩),
   opAt 2932 .ADD,
   opAt 2933 (.Dup ⟨0, by decide⟩),
   opAt 2934 (.Swap ⟨5, by decide⟩),
   opAt 2935 .GT,
   opAt 2936 .SUB,
   opAt 2937 .SUB,
   opAt 2938 (.Dup ⟨3, by decide⟩),
   opAt 2939 (.Dup ⟨3, by decide⟩),
   opAt 2940 .MLOAD,
   opAt 2941 .ADD,
   opAt 2942 (.Dup ⟨0, by decide⟩),
   opAt 2943 (.Swap ⟨4, by decide⟩),
   opAt 2944 .GT,
   opAt 2945 .ADD,
   opAt 2946 (.Swap ⟨2, by decide⟩),
   opAt 2947 (.Dup ⟨2, by decide⟩),
   pushAt 2948 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2949 .ADD,
   opAt 2950 (.Swap ⟨2, by decide⟩),
   opAt 2951 .MSTORE,
   pushAt 2952 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2953 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2954 2 8224,
   opAt 2955 (.Dup ⟨2, by decide⟩),
   opAt 2956 .GT,
   pushAt 2957 2 4952,
   opAt 2958 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2991 .JUMPDEST,
   opAt 2992 (.Dup ⟨0, by decide⟩),
   opAt 2993 .MLOAD,
   opAt 2994 (.Dup ⟨1, by decide⟩),
   pushAt 2995 2 8256,
   opAt 2996 (.Swap ⟨0, by decide⟩),
   opAt 2997 .SUB,
   opAt 2998 .MLOAD,
   opAt 2999 (.Dup ⟨1, by decide⟩),
   opAt 3000 .ADD,
   opAt 3001 (.Dup ⟨0, by decide⟩),
   opAt 3002 (.Dup ⟨2, by decide⟩),
   opAt 3003 .GT,
   opAt 3004 (.Swap ⟨1, by decide⟩),
   opAt 3005 .POP,
   opAt 3006 (.Dup ⟨3, by decide⟩),
   opAt 3007 .ADD,
   opAt 3008 (.Dup ⟨0, by decide⟩),
   opAt 3009 (.Dup ⟨4, by decide⟩),
   opAt 3010 .GT,
   opAt 3011 (.Swap ⟨3, by decide⟩),
   opAt 3012 .POP,
   opAt 3013 (.Dup ⟨2, by decide⟩),
   opAt 3014 .MSTORE,
   opAt 3015 (.Swap ⟨0, by decide⟩),
   opAt 3016 (.Swap ⟨1, by decide⟩),
   opAt 3017 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3018 (.Swap ⟨0, by decide⟩),
   pushAt 3019 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3020 .ADD,
   pushAt 3021 2 8255,
   opAt 3022 (.Dup ⟨1, by decide⟩),
   opAt 3023 .GT,
   pushAt 3024 2 5135,
   opAt 3025 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
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
   opAt 3056 (.Dup ⟨1, by decide⟩),
   opAt 3057 .GT,
   opAt 3058 (.Swap ⟨1, by decide⟩),
   opAt 3059 .SUB,
   opAt 3060 (.Dup ⟨3, by decide⟩),
   opAt 3061 (.Dup ⟨1, by decide⟩),
   opAt 3062 .LT,
   opAt 3063 (.Swap ⟨0, by decide⟩),
   opAt 3064 (.Dup ⟨4, by decide⟩),
   opAt 3065 (.Swap ⟨0, by decide⟩),
   opAt 3066 .SUB,
   opAt 3067 (.Dup ⟨3, by decide⟩),
   opAt 3068 .MSTORE,
   opAt 3069 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3070 (.Swap ⟨1, by decide⟩),
   opAt 3071 .POP,
   pushAt 3072 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3073 .ADD,
   pushAt 3074 2 8255,
   opAt 3075 (.Dup ⟨1, by decide⟩),
   opAt 3076 .GT,
   pushAt 3077 2 5241,
   opAt 3078 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
