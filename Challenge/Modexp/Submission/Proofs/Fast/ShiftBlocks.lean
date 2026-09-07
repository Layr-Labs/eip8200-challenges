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
  [opAt 2768 .JUMPDEST,
   opAt 2769 (.Dup ⟨0, by decide⟩),
   opAt 2770 .MLOAD,
   opAt 2771 .NOT,
   opAt 2772 (.Dup ⟨2, by decide⟩),
   opAt 2773 .ADD,
   opAt 2774 (.Dup ⟨2, by decide⟩),
   opAt 2775 (.Dup ⟨1, by decide⟩),
   opAt 2776 .LT,
   opAt 2777 (.Swap ⟨2, by decide⟩),
   opAt 2778 .POP,
   opAt 2779 (.Dup ⟨1, by decide⟩),
   pushAt 2780 2 5120,
   opAt 2781 .ADD,
   opAt 2782 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2783 (.Dup ⟨0, by decide⟩),
   opAt 2784 .ISZERO,
   pushAt 2785 2 4735,
   opAt 2786 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2956 .JUMPDEST,
   opAt 2957 (.Dup ⟨0, by decide⟩),
   opAt 2958 .MLOAD,
   pushAt 2959 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2960 (.Dup ⟨5, by decide⟩),
   opAt 2961 (.Dup ⟨2, by decide⟩),
   opAt 2962 .MUL,
   opAt 2963 (.Swap ⟨1, by decide⟩),
   opAt 2964 (.Dup ⟨6, by decide⟩),
   opAt 2965 .MULMOD,
   opAt 2966 (.Dup ⟨1, by decide⟩),
   opAt 2967 (.Dup ⟨1, by decide⟩),
   opAt 2968 .LT,
   opAt 2969 .SUB,
   opAt 2970 (.Dup ⟨4, by decide⟩),
   opAt 2971 (.Dup ⟨2, by decide⟩),
   opAt 2972 .ADD,
   opAt 2973 (.Dup ⟨0, by decide⟩),
   opAt 2974 (.Swap ⟨5, by decide⟩),
   opAt 2975 .GT,
   opAt 2976 .SUB,
   opAt 2977 .SUB,
   opAt 2978 (.Dup ⟨3, by decide⟩),
   opAt 2979 (.Dup ⟨3, by decide⟩),
   opAt 2980 .MLOAD,
   opAt 2981 .ADD,
   opAt 2982 (.Dup ⟨0, by decide⟩),
   opAt 2983 (.Swap ⟨4, by decide⟩),
   opAt 2984 .GT,
   opAt 2985 .ADD,
   opAt 2986 (.Swap ⟨2, by decide⟩),
   opAt 2987 (.Dup ⟨2, by decide⟩),
   pushAt 2988 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2989 .ADD,
   opAt 2990 (.Swap ⟨2, by decide⟩),
   opAt 2991 .MSTORE,
   pushAt 2992 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2993 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2994 2 8224,
   opAt 2995 (.Dup ⟨2, by decide⟩),
   opAt 2996 .GT,
   pushAt 2997 2 4952,
   opAt 2998 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3031 .JUMPDEST,
   opAt 3032 (.Dup ⟨0, by decide⟩),
   opAt 3033 .MLOAD,
   opAt 3034 (.Dup ⟨1, by decide⟩),
   pushAt 3035 2 8256,
   opAt 3036 (.Swap ⟨0, by decide⟩),
   opAt 3037 .SUB,
   opAt 3038 .MLOAD,
   opAt 3039 (.Dup ⟨1, by decide⟩),
   opAt 3040 .ADD,
   opAt 3041 (.Dup ⟨0, by decide⟩),
   opAt 3042 (.Dup ⟨2, by decide⟩),
   opAt 3043 .GT,
   opAt 3044 (.Swap ⟨1, by decide⟩),
   opAt 3045 .POP,
   opAt 3046 (.Dup ⟨3, by decide⟩),
   opAt 3047 .ADD,
   opAt 3048 (.Dup ⟨0, by decide⟩),
   opAt 3049 (.Dup ⟨4, by decide⟩),
   opAt 3050 .GT,
   opAt 3051 (.Swap ⟨3, by decide⟩),
   opAt 3052 .POP,
   opAt 3053 (.Dup ⟨2, by decide⟩),
   opAt 3054 .MSTORE,
   opAt 3055 (.Swap ⟨0, by decide⟩),
   opAt 3056 (.Swap ⟨1, by decide⟩),
   opAt 3057 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3058 (.Swap ⟨0, by decide⟩),
   pushAt 3059 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3060 .ADD,
   pushAt 3061 2 8255,
   opAt 3062 (.Dup ⟨1, by decide⟩),
   opAt 3063 .GT,
   pushAt 3064 2 5135,
   opAt 3065 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3087 .JUMPDEST,
   opAt 3088 (.Dup ⟨0, by decide⟩),
   opAt 3089 .MLOAD,
   opAt 3090 (.Dup ⟨1, by decide⟩),
   pushAt 3091 2 8256,
   opAt 3092 (.Swap ⟨0, by decide⟩),
   opAt 3093 .SUB,
   opAt 3094 .MLOAD,
   opAt 3095 (.Dup ⟨1, by decide⟩),
   opAt 3096 (.Dup ⟨1, by decide⟩),
   opAt 3097 .GT,
   opAt 3098 (.Swap ⟨1, by decide⟩),
   opAt 3099 .SUB,
   opAt 3100 (.Dup ⟨3, by decide⟩),
   opAt 3101 (.Dup ⟨1, by decide⟩),
   opAt 3102 .LT,
   opAt 3103 (.Swap ⟨0, by decide⟩),
   opAt 3104 (.Dup ⟨4, by decide⟩),
   opAt 3105 (.Swap ⟨0, by decide⟩),
   opAt 3106 .SUB,
   opAt 3107 (.Dup ⟨3, by decide⟩),
   opAt 3108 .MSTORE,
   opAt 3109 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3110 (.Swap ⟨1, by decide⟩),
   opAt 3111 .POP,
   pushAt 3112 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3113 .ADD,
   pushAt 3114 2 8255,
   opAt 3115 (.Dup ⟨1, by decide⟩),
   opAt 3116 .GT,
   pushAt 3117 2 5241,
   opAt 3118 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
