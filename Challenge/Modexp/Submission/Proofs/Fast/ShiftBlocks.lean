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
  [opAt 2752 .JUMPDEST,
   opAt 2753 (.Dup ⟨0, by decide⟩),
   opAt 2754 .MLOAD,
   opAt 2755 .NOT,
   opAt 2756 (.Dup ⟨2, by decide⟩),
   opAt 2757 .ADD,
   opAt 2758 (.Dup ⟨2, by decide⟩),
   opAt 2759 (.Dup ⟨1, by decide⟩),
   opAt 2760 .LT,
   opAt 2761 (.Swap ⟨2, by decide⟩),
   opAt 2762 .POP,
   opAt 2763 (.Dup ⟨1, by decide⟩),
   pushAt 2764 2 5120,
   opAt 2765 .ADD,
   opAt 2766 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2767 (.Dup ⟨0, by decide⟩),
   opAt 2768 .ISZERO,
   pushAt 2769 2 4735,
   opAt 2770 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2940 .JUMPDEST,
   opAt 2941 (.Dup ⟨0, by decide⟩),
   opAt 2942 .MLOAD,
   pushAt 2943 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2944 (.Dup ⟨5, by decide⟩),
   opAt 2945 (.Dup ⟨2, by decide⟩),
   opAt 2946 .MUL,
   opAt 2947 (.Swap ⟨1, by decide⟩),
   opAt 2948 (.Dup ⟨6, by decide⟩),
   opAt 2949 .MULMOD,
   opAt 2950 (.Dup ⟨1, by decide⟩),
   opAt 2951 (.Dup ⟨1, by decide⟩),
   opAt 2952 .LT,
   opAt 2953 .SUB,
   opAt 2954 (.Dup ⟨4, by decide⟩),
   opAt 2955 (.Dup ⟨2, by decide⟩),
   opAt 2956 .ADD,
   opAt 2957 (.Dup ⟨0, by decide⟩),
   opAt 2958 (.Swap ⟨5, by decide⟩),
   opAt 2959 .GT,
   opAt 2960 .SUB,
   opAt 2961 .SUB,
   opAt 2962 (.Dup ⟨3, by decide⟩),
   opAt 2963 (.Dup ⟨3, by decide⟩),
   opAt 2964 .MLOAD,
   opAt 2965 .ADD,
   opAt 2966 (.Dup ⟨0, by decide⟩),
   opAt 2967 (.Swap ⟨4, by decide⟩),
   opAt 2968 .GT,
   opAt 2969 .ADD,
   opAt 2970 (.Swap ⟨2, by decide⟩),
   opAt 2971 (.Dup ⟨2, by decide⟩),
   pushAt 2972 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2973 .ADD,
   opAt 2974 (.Swap ⟨2, by decide⟩),
   opAt 2975 .MSTORE,
   pushAt 2976 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2977 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2978 2 8224,
   opAt 2979 (.Dup ⟨2, by decide⟩),
   opAt 2980 .GT,
   pushAt 2981 2 4952,
   opAt 2982 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3015 .JUMPDEST,
   opAt 3016 (.Dup ⟨0, by decide⟩),
   opAt 3017 .MLOAD,
   opAt 3018 (.Dup ⟨1, by decide⟩),
   pushAt 3019 2 8256,
   opAt 3020 (.Swap ⟨0, by decide⟩),
   opAt 3021 .SUB,
   opAt 3022 .MLOAD,
   opAt 3023 (.Dup ⟨1, by decide⟩),
   opAt 3024 .ADD,
   opAt 3025 (.Dup ⟨0, by decide⟩),
   opAt 3026 (.Dup ⟨2, by decide⟩),
   opAt 3027 .GT,
   opAt 3028 (.Swap ⟨1, by decide⟩),
   opAt 3029 .POP,
   opAt 3030 (.Dup ⟨3, by decide⟩),
   opAt 3031 .ADD,
   opAt 3032 (.Dup ⟨0, by decide⟩),
   opAt 3033 (.Dup ⟨4, by decide⟩),
   opAt 3034 .GT,
   opAt 3035 (.Swap ⟨3, by decide⟩),
   opAt 3036 .POP,
   opAt 3037 (.Dup ⟨2, by decide⟩),
   opAt 3038 .MSTORE,
   opAt 3039 (.Swap ⟨0, by decide⟩),
   opAt 3040 (.Swap ⟨1, by decide⟩),
   opAt 3041 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3042 (.Swap ⟨0, by decide⟩),
   pushAt 3043 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3044 .ADD,
   pushAt 3045 2 8255,
   opAt 3046 (.Dup ⟨1, by decide⟩),
   opAt 3047 .GT,
   pushAt 3048 2 5135,
   opAt 3049 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3071 .JUMPDEST,
   opAt 3072 (.Dup ⟨0, by decide⟩),
   opAt 3073 .MLOAD,
   opAt 3074 (.Dup ⟨1, by decide⟩),
   pushAt 3075 2 8256,
   opAt 3076 (.Swap ⟨0, by decide⟩),
   opAt 3077 .SUB,
   opAt 3078 .MLOAD,
   opAt 3079 (.Dup ⟨1, by decide⟩),
   opAt 3080 (.Dup ⟨1, by decide⟩),
   opAt 3081 .GT,
   opAt 3082 (.Swap ⟨1, by decide⟩),
   opAt 3083 .SUB,
   opAt 3084 (.Dup ⟨3, by decide⟩),
   opAt 3085 (.Dup ⟨1, by decide⟩),
   opAt 3086 .LT,
   opAt 3087 (.Swap ⟨0, by decide⟩),
   opAt 3088 (.Dup ⟨4, by decide⟩),
   opAt 3089 (.Swap ⟨0, by decide⟩),
   opAt 3090 .SUB,
   opAt 3091 (.Dup ⟨3, by decide⟩),
   opAt 3092 .MSTORE,
   opAt 3093 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3094 (.Swap ⟨1, by decide⟩),
   opAt 3095 .POP,
   pushAt 3096 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3097 .ADD,
   pushAt 3098 2 8255,
   opAt 3099 (.Dup ⟨1, by decide⟩),
   opAt 3100 .GT,
   pushAt 3101 2 5241,
   opAt 3102 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
