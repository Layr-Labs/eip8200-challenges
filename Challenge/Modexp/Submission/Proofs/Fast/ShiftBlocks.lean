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
  [opAt 2939 .JUMPDEST,
   opAt 2940 (.Dup ⟨0, by decide⟩),
   opAt 2941 .MLOAD,
   pushAt 2942 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2943 (.Dup ⟨5, by decide⟩),
   opAt 2944 (.Dup ⟨2, by decide⟩),
   opAt 2945 .MUL,
   opAt 2946 (.Swap ⟨1, by decide⟩),
   opAt 2947 (.Dup ⟨6, by decide⟩),
   opAt 2948 .MULMOD,
   opAt 2949 (.Dup ⟨1, by decide⟩),
   opAt 2950 (.Dup ⟨1, by decide⟩),
   opAt 2951 .LT,
   opAt 2952 .SUB,
   opAt 2953 (.Dup ⟨4, by decide⟩),
   opAt 2954 (.Dup ⟨2, by decide⟩),
   opAt 2955 .ADD,
   opAt 2956 (.Dup ⟨0, by decide⟩),
   opAt 2957 (.Swap ⟨5, by decide⟩),
   opAt 2958 .GT,
   opAt 2959 .SUB,
   opAt 2960 .SUB,
   opAt 2961 (.Dup ⟨3, by decide⟩),
   opAt 2962 (.Dup ⟨3, by decide⟩),
   opAt 2963 .MLOAD,
   opAt 2964 .ADD,
   opAt 2965 (.Dup ⟨0, by decide⟩),
   opAt 2966 (.Swap ⟨4, by decide⟩),
   opAt 2967 .GT,
   opAt 2968 .ADD,
   opAt 2969 (.Swap ⟨2, by decide⟩),
   opAt 2970 (.Dup ⟨2, by decide⟩),
   pushAt 2971 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2972 .ADD,
   opAt 2973 (.Swap ⟨2, by decide⟩),
   opAt 2974 .MSTORE,
   pushAt 2975 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2976 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2977 2 8224,
   opAt 2978 (.Dup ⟨2, by decide⟩),
   opAt 2979 .GT,
   pushAt 2980 2 4951,
   opAt 2981 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3014 .JUMPDEST,
   opAt 3015 (.Dup ⟨0, by decide⟩),
   opAt 3016 .MLOAD,
   opAt 3017 (.Dup ⟨1, by decide⟩),
   pushAt 3018 2 8256,
   opAt 3019 (.Swap ⟨0, by decide⟩),
   opAt 3020 .SUB,
   opAt 3021 .MLOAD,
   opAt 3022 (.Dup ⟨1, by decide⟩),
   opAt 3023 .ADD,
   opAt 3024 (.Dup ⟨0, by decide⟩),
   opAt 3025 (.Dup ⟨2, by decide⟩),
   opAt 3026 .GT,
   opAt 3027 (.Swap ⟨1, by decide⟩),
   opAt 3028 .POP,
   opAt 3029 (.Dup ⟨3, by decide⟩),
   opAt 3030 .ADD,
   opAt 3031 (.Dup ⟨0, by decide⟩),
   opAt 3032 (.Dup ⟨4, by decide⟩),
   opAt 3033 .GT,
   opAt 3034 (.Swap ⟨3, by decide⟩),
   opAt 3035 .POP,
   opAt 3036 (.Dup ⟨2, by decide⟩),
   opAt 3037 .MSTORE,
   opAt 3038 (.Swap ⟨0, by decide⟩),
   opAt 3039 (.Swap ⟨1, by decide⟩),
   opAt 3040 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3041 (.Swap ⟨0, by decide⟩),
   pushAt 3042 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3043 .ADD,
   pushAt 3044 2 8255,
   opAt 3045 (.Dup ⟨1, by decide⟩),
   opAt 3046 .GT,
   pushAt 3047 2 5134,
   opAt 3048 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3070 .JUMPDEST,
   opAt 3071 (.Dup ⟨0, by decide⟩),
   opAt 3072 .MLOAD,
   opAt 3073 (.Dup ⟨1, by decide⟩),
   pushAt 3074 2 8256,
   opAt 3075 (.Swap ⟨0, by decide⟩),
   opAt 3076 .SUB,
   opAt 3077 .MLOAD,
   opAt 3078 (.Dup ⟨1, by decide⟩),
   opAt 3079 (.Dup ⟨1, by decide⟩),
   opAt 3080 .GT,
   opAt 3081 (.Swap ⟨1, by decide⟩),
   opAt 3082 .SUB,
   opAt 3083 (.Dup ⟨3, by decide⟩),
   opAt 3084 (.Dup ⟨1, by decide⟩),
   opAt 3085 .LT,
   opAt 3086 (.Swap ⟨0, by decide⟩),
   opAt 3087 (.Dup ⟨4, by decide⟩),
   opAt 3088 (.Swap ⟨0, by decide⟩),
   opAt 3089 .SUB,
   opAt 3090 (.Dup ⟨3, by decide⟩),
   opAt 3091 .MSTORE,
   opAt 3092 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3093 (.Swap ⟨1, by decide⟩),
   opAt 3094 .POP,
   pushAt 3095 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3096 .ADD,
   pushAt 3097 2 8255,
   opAt 3098 (.Dup ⟨1, by decide⟩),
   opAt 3099 .GT,
   pushAt 3100 2 5240,
   opAt 3101 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
