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
  [opAt 2759 .JUMPDEST,
   opAt 2760 (.Dup ⟨0, by decide⟩),
   opAt 2761 .MLOAD,
   opAt 2762 .NOT,
   opAt 2763 (.Dup ⟨2, by decide⟩),
   opAt 2764 .ADD,
   opAt 2765 (.Dup ⟨2, by decide⟩),
   opAt 2766 (.Dup ⟨1, by decide⟩),
   opAt 2767 .LT,
   opAt 2768 (.Swap ⟨2, by decide⟩),
   opAt 2769 .POP,
   opAt 2770 (.Dup ⟨1, by decide⟩),
   pushAt 2771 2 5120,
   opAt 2772 .ADD,
   opAt 2773 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2774 (.Dup ⟨0, by decide⟩),
   opAt 2775 .ISZERO,
   pushAt 2776 2 3867,
   opAt 2777 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2947 .JUMPDEST,
   opAt 2948 (.Dup ⟨0, by decide⟩),
   opAt 2949 .MLOAD,
   pushAt 2950 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2951 (.Dup ⟨5, by decide⟩),
   opAt 2952 (.Dup ⟨2, by decide⟩),
   opAt 2953 .MUL,
   opAt 2954 (.Swap ⟨1, by decide⟩),
   opAt 2955 (.Dup ⟨6, by decide⟩),
   opAt 2956 .MULMOD,
   opAt 2957 (.Dup ⟨1, by decide⟩),
   opAt 2958 (.Dup ⟨1, by decide⟩),
   opAt 2959 .LT,
   opAt 2960 .SUB,
   opAt 2961 (.Dup ⟨4, by decide⟩),
   opAt 2962 (.Dup ⟨2, by decide⟩),
   opAt 2963 .ADD,
   opAt 2964 (.Dup ⟨0, by decide⟩),
   opAt 2965 (.Swap ⟨5, by decide⟩),
   opAt 2966 .GT,
   opAt 2967 .SUB,
   opAt 2968 .SUB,
   opAt 2969 (.Dup ⟨3, by decide⟩),
   opAt 2970 (.Dup ⟨3, by decide⟩),
   opAt 2971 .MLOAD,
   opAt 2972 .ADD,
   opAt 2973 (.Dup ⟨0, by decide⟩),
   opAt 2974 (.Swap ⟨4, by decide⟩),
   opAt 2975 .GT,
   opAt 2976 .ADD,
   opAt 2977 (.Swap ⟨2, by decide⟩),
   opAt 2978 (.Dup ⟨2, by decide⟩),
   pushAt 2979 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2980 .ADD,
   opAt 2981 (.Swap ⟨2, by decide⟩),
   opAt 2982 .MSTORE,
   pushAt 2983 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2984 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2985 2 8224,
   opAt 2986 (.Dup ⟨2, by decide⟩),
   opAt 2987 .GT,
   pushAt 2988 2 4089,
   opAt 2989 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3022 .JUMPDEST,
   opAt 3023 (.Dup ⟨0, by decide⟩),
   opAt 3024 .MLOAD,
   opAt 3025 (.Dup ⟨1, by decide⟩),
   pushAt 3026 2 8256,
   opAt 3027 (.Swap ⟨0, by decide⟩),
   opAt 3028 .SUB,
   opAt 3029 .MLOAD,
   opAt 3030 (.Dup ⟨1, by decide⟩),
   opAt 3031 .ADD,
   opAt 3032 (.Dup ⟨0, by decide⟩),
   opAt 3033 (.Dup ⟨2, by decide⟩),
   opAt 3034 .GT,
   opAt 3035 (.Swap ⟨1, by decide⟩),
   opAt 3036 .POP,
   opAt 3037 (.Dup ⟨3, by decide⟩),
   opAt 3038 .ADD,
   opAt 3039 (.Dup ⟨0, by decide⟩),
   opAt 3040 (.Dup ⟨4, by decide⟩),
   opAt 3041 .GT,
   opAt 3042 (.Swap ⟨3, by decide⟩),
   opAt 3043 .POP,
   opAt 3044 (.Dup ⟨2, by decide⟩),
   opAt 3045 .MSTORE,
   opAt 3046 (.Swap ⟨0, by decide⟩),
   opAt 3047 (.Swap ⟨1, by decide⟩),
   opAt 3048 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3049 (.Swap ⟨0, by decide⟩),
   pushAt 3050 1 31,
   opAt 3051 .NOT,
   opAt 3052 .ADD,
   pushAt 3053 2 8255,
   opAt 3054 (.Dup ⟨1, by decide⟩),
   opAt 3055 .GT,
   pushAt 3056 2 4272,
   opAt 3057 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3079 .JUMPDEST,
   opAt 3080 (.Dup ⟨0, by decide⟩),
   opAt 3081 .MLOAD,
   opAt 3082 (.Dup ⟨1, by decide⟩),
   pushAt 3083 2 8256,
   opAt 3084 (.Swap ⟨0, by decide⟩),
   opAt 3085 .SUB,
   opAt 3086 .MLOAD,
   opAt 3087 (.Dup ⟨1, by decide⟩),
   opAt 3088 (.Dup ⟨1, by decide⟩),
   opAt 3089 .GT,
   opAt 3090 (.Swap ⟨1, by decide⟩),
   opAt 3091 .SUB,
   opAt 3092 (.Dup ⟨3, by decide⟩),
   opAt 3093 (.Dup ⟨1, by decide⟩),
   opAt 3094 .LT,
   opAt 3095 (.Swap ⟨0, by decide⟩),
   opAt 3096 (.Dup ⟨4, by decide⟩),
   opAt 3097 (.Swap ⟨0, by decide⟩),
   opAt 3098 .SUB,
   opAt 3099 (.Dup ⟨3, by decide⟩),
   opAt 3100 .MSTORE,
   opAt 3101 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3102 (.Swap ⟨1, by decide⟩),
   opAt 3103 .POP,
   pushAt 3104 1 31,
   opAt 3105 .NOT,
   opAt 3106 .ADD,
   pushAt 3107 2 8255,
   opAt 3108 (.Dup ⟨1, by decide⟩),
   opAt 3109 .GT,
   pushAt 3110 2 4348,
   opAt 3111 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
