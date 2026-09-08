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
  [opAt 2729 .JUMPDEST,
   opAt 2730 (.Dup ⟨0, by decide⟩),
   opAt 2731 .MLOAD,
   opAt 2732 .NOT,
   opAt 2733 (.Dup ⟨2, by decide⟩),
   opAt 2734 .ADD,
   opAt 2735 (.Dup ⟨2, by decide⟩),
   opAt 2736 (.Dup ⟨1, by decide⟩),
   opAt 2737 .LT,
   opAt 2738 (.Swap ⟨2, by decide⟩),
   opAt 2739 .POP,
   opAt 2740 (.Dup ⟨1, by decide⟩),
   pushAt 2741 2 5120,
   opAt 2742 .ADD,
   opAt 2743 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2744 (.Dup ⟨0, by decide⟩),
   opAt 2745 .ISZERO,
   pushAt 2746 2 4135,
   opAt 2747 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2918 .JUMPDEST,
   opAt 2919 (.Dup ⟨0, by decide⟩),
   opAt 2920 .MLOAD,
   pushAt 2921 1 0, opAt 2922 .NOT,
   opAt 2923 (.Dup ⟨5, by decide⟩),
   opAt 2924 (.Dup ⟨2, by decide⟩),
   opAt 2925 .MUL,
   opAt 2926 (.Swap ⟨1, by decide⟩),
   opAt 2927 (.Dup ⟨6, by decide⟩),
   opAt 2928 .MULMOD,
   opAt 2929 (.Dup ⟨1, by decide⟩),
   opAt 2930 (.Dup ⟨1, by decide⟩),
   opAt 2931 .LT,
   opAt 2932 .SUB,
   opAt 2933 (.Dup ⟨4, by decide⟩),
   opAt 2934 (.Dup ⟨2, by decide⟩),
   opAt 2935 .ADD,
   opAt 2936 (.Dup ⟨0, by decide⟩),
   opAt 2937 (.Swap ⟨5, by decide⟩),
   opAt 2938 .GT,
   opAt 2939 .SUB,
   opAt 2940 .SUB,
   opAt 2941 (.Dup ⟨3, by decide⟩),
   opAt 2942 (.Dup ⟨3, by decide⟩),
   opAt 2943 .MLOAD,
   opAt 2944 .ADD,
   opAt 2945 (.Dup ⟨0, by decide⟩),
   opAt 2946 (.Swap ⟨4, by decide⟩),
   opAt 2947 .GT,
   opAt 2948 .ADD,
   opAt 2949 (.Swap ⟨2, by decide⟩),
   opAt 2950 (.Dup ⟨2, by decide⟩),
   pushAt 2951 1 31, opAt 2952 .NOT,
   opAt 2953 .ADD,
   opAt 2954 (.Swap ⟨2, by decide⟩),
   opAt 2955 .MSTORE,
   pushAt 2956 1 31, opAt 2957 .NOT,
   opAt 2958 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2959 2 8224,
   opAt 2960 (.Dup ⟨2, by decide⟩),
   opAt 2961 .GT,
   pushAt 2962 2 4352,
   opAt 2963 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2996 .JUMPDEST,
   opAt 2997 (.Dup ⟨0, by decide⟩),
   opAt 2998 .MLOAD,
   opAt 2999 (.Dup ⟨1, by decide⟩),
   pushAt 3000 2 8256,
   opAt 3001 (.Swap ⟨0, by decide⟩),
   opAt 3002 .SUB,
   opAt 3003 .MLOAD,
   opAt 3004 (.Dup ⟨1, by decide⟩),
   opAt 3005 .ADD,
   opAt 3006 (.Dup ⟨0, by decide⟩),
   opAt 3007 (.Dup ⟨2, by decide⟩),
   opAt 3008 .GT,
   opAt 3009 (.Swap ⟨1, by decide⟩),
   opAt 3010 .POP,
   opAt 3011 (.Dup ⟨3, by decide⟩),
   opAt 3012 .ADD,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 (.Dup ⟨4, by decide⟩),
   opAt 3015 .GT,
   opAt 3016 (.Swap ⟨3, by decide⟩),
   opAt 3017 .POP,
   opAt 3018 (.Dup ⟨2, by decide⟩),
   opAt 3019 .MSTORE,
   opAt 3020 (.Swap ⟨0, by decide⟩),
   opAt 3021 (.Swap ⟨1, by decide⟩),
   opAt 3022 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3023 (.Swap ⟨0, by decide⟩),
   pushAt 3024 1 31, opAt 3025 .NOT,
   opAt 3026 .ADD,
   pushAt 3027 2 8255,
   opAt 3028 (.Dup ⟨1, by decide⟩),
   opAt 3029 .GT,
   pushAt 3030 2 4445,
   opAt 3031 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3053 .JUMPDEST,
   opAt 3054 (.Dup ⟨0, by decide⟩),
   opAt 3055 .MLOAD,
   opAt 3056 (.Dup ⟨1, by decide⟩),
   pushAt 3057 2 8256,
   opAt 3058 (.Swap ⟨0, by decide⟩),
   opAt 3059 .SUB,
   opAt 3060 .MLOAD,
   opAt 3061 (.Dup ⟨1, by decide⟩),
   opAt 3062 (.Dup ⟨1, by decide⟩),
   opAt 3063 .GT,
   opAt 3064 (.Swap ⟨1, by decide⟩),
   opAt 3065 .SUB,
   opAt 3066 (.Dup ⟨3, by decide⟩),
   opAt 3067 (.Dup ⟨1, by decide⟩),
   opAt 3068 .LT,
   opAt 3069 (.Swap ⟨0, by decide⟩),
   opAt 3070 (.Dup ⟨4, by decide⟩),
   opAt 3071 (.Swap ⟨0, by decide⟩),
   opAt 3072 .SUB,
   opAt 3073 (.Dup ⟨3, by decide⟩),
   opAt 3074 .MSTORE,
   opAt 3075 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3076 (.Swap ⟨1, by decide⟩),
   opAt 3077 .POP,
   pushAt 3078 1 31, opAt 3079 .NOT,
   opAt 3080 .ADD,
   pushAt 3081 2 8255,
   opAt 3082 (.Dup ⟨1, by decide⟩),
   opAt 3083 .GT,
   pushAt 3084 2 4521,
   opAt 3085 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
