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
  [opAt 2741 .JUMPDEST,
   opAt 2742 (.Dup ⟨0, by decide⟩),
   opAt 2743 .MLOAD,
   opAt 2744 .NOT,
   opAt 2745 (.Dup ⟨2, by decide⟩),
   opAt 2746 .ADD,
   opAt 2747 (.Dup ⟨2, by decide⟩),
   opAt 2748 (.Dup ⟨1, by decide⟩),
   opAt 2749 .LT,
   opAt 2750 (.Swap ⟨2, by decide⟩),
   opAt 2751 .POP,
   opAt 2752 (.Dup ⟨1, by decide⟩),
   pushAt 2753 2 5120,
   opAt 2754 .ADD,
   opAt 2755 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2756 (.Dup ⟨0, by decide⟩),
   opAt 2757 .ISZERO,
   pushAt 2758 2 4588,
   opAt 2759 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2928 .JUMPDEST,
   opAt 2929 (.Dup ⟨0, by decide⟩),
   opAt 2930 .MLOAD,
   pushAt 2931 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2932 (.Dup ⟨5, by decide⟩),
   opAt 2933 (.Dup ⟨2, by decide⟩),
   opAt 2934 .MUL,
   opAt 2935 (.Swap ⟨1, by decide⟩),
   opAt 2936 (.Dup ⟨6, by decide⟩),
   opAt 2937 .MULMOD,
   opAt 2938 (.Dup ⟨1, by decide⟩),
   opAt 2939 (.Dup ⟨1, by decide⟩),
   opAt 2940 .LT,
   opAt 2941 .SUB,
   opAt 2942 (.Dup ⟨4, by decide⟩),
   opAt 2943 (.Dup ⟨2, by decide⟩),
   opAt 2944 .ADD,
   opAt 2945 (.Dup ⟨0, by decide⟩),
   opAt 2946 (.Swap ⟨5, by decide⟩),
   opAt 2947 .GT,
   opAt 2948 .SUB,
   opAt 2949 .SUB,
   opAt 2950 (.Dup ⟨3, by decide⟩),
   opAt 2951 (.Dup ⟨3, by decide⟩),
   opAt 2952 .MLOAD,
   opAt 2953 .ADD,
   opAt 2954 (.Dup ⟨0, by decide⟩),
   opAt 2955 (.Swap ⟨4, by decide⟩),
   opAt 2956 .GT,
   opAt 2957 .ADD,
   opAt 2958 (.Swap ⟨2, by decide⟩),
   opAt 2959 (.Dup ⟨2, by decide⟩),
   pushAt 2960 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2961 .ADD,
   opAt 2962 (.Swap ⟨2, by decide⟩),
   opAt 2963 .MSTORE,
   pushAt 2964 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2965 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2966 2 8224,
   opAt 2967 (.Dup ⟨2, by decide⟩),
   opAt 2968 .GT,
   pushAt 2969 2 4804,
   opAt 2970 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3003 .JUMPDEST,
   opAt 3004 (.Dup ⟨0, by decide⟩),
   opAt 3005 .MLOAD,
   opAt 3006 (.Dup ⟨1, by decide⟩),
   pushAt 3007 2 8256,
   opAt 3008 (.Swap ⟨0, by decide⟩),
   opAt 3009 .SUB,
   opAt 3010 .MLOAD,
   opAt 3011 (.Dup ⟨1, by decide⟩),
   opAt 3012 .ADD,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 (.Dup ⟨2, by decide⟩),
   opAt 3015 .GT,
   opAt 3016 (.Swap ⟨1, by decide⟩),
   opAt 3017 .POP,
   opAt 3018 (.Dup ⟨3, by decide⟩),
   opAt 3019 .ADD,
   opAt 3020 (.Dup ⟨0, by decide⟩),
   opAt 3021 (.Dup ⟨4, by decide⟩),
   opAt 3022 .GT,
   opAt 3023 (.Swap ⟨3, by decide⟩),
   opAt 3024 .POP,
   opAt 3025 (.Dup ⟨2, by decide⟩),
   opAt 3026 .MSTORE,
   opAt 3027 (.Swap ⟨0, by decide⟩),
   opAt 3028 (.Swap ⟨1, by decide⟩),
   opAt 3029 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3030 (.Swap ⟨0, by decide⟩),
   pushAt 3031 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3032 .ADD,
   pushAt 3033 2 8255,
   opAt 3034 (.Dup ⟨1, by decide⟩),
   opAt 3035 .GT,
   pushAt 3036 2 4987,
   opAt 3037 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3059 .JUMPDEST,
   opAt 3060 (.Dup ⟨0, by decide⟩),
   opAt 3061 .MLOAD,
   opAt 3062 (.Dup ⟨1, by decide⟩),
   pushAt 3063 2 8256,
   opAt 3064 (.Swap ⟨0, by decide⟩),
   opAt 3065 .SUB,
   opAt 3066 .MLOAD,
   opAt 3067 (.Dup ⟨1, by decide⟩),
   opAt 3068 (.Dup ⟨1, by decide⟩),
   opAt 3069 .GT,
   opAt 3070 (.Swap ⟨1, by decide⟩),
   opAt 3071 .SUB,
   opAt 3072 (.Dup ⟨3, by decide⟩),
   opAt 3073 (.Dup ⟨1, by decide⟩),
   opAt 3074 .LT,
   opAt 3075 (.Swap ⟨0, by decide⟩),
   opAt 3076 (.Dup ⟨4, by decide⟩),
   opAt 3077 (.Swap ⟨0, by decide⟩),
   opAt 3078 .SUB,
   opAt 3079 (.Dup ⟨3, by decide⟩),
   opAt 3080 .MSTORE,
   opAt 3081 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3082 (.Swap ⟨1, by decide⟩),
   opAt 3083 .POP,
   pushAt 3084 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3085 .ADD,
   pushAt 3086 2 8255,
   opAt 3087 (.Dup ⟨1, by decide⟩),
   opAt 3088 .GT,
   pushAt 3089 2 5093,
   opAt 3090 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
