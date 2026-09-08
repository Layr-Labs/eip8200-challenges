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
  [opAt 2718 .JUMPDEST,
   opAt 2719 (.Dup ⟨0, by decide⟩),
   opAt 2720 .MLOAD,
   opAt 2721 .NOT,
   opAt 2722 (.Dup ⟨2, by decide⟩),
   opAt 2723 .ADD,
   opAt 2724 (.Dup ⟨2, by decide⟩),
   opAt 2725 (.Dup ⟨1, by decide⟩),
   opAt 2726 .LT,
   opAt 2727 (.Swap ⟨2, by decide⟩),
   opAt 2728 .POP,
   opAt 2729 (.Dup ⟨1, by decide⟩),
   pushAt 2730 2 5120,
   opAt 2731 .ADD,
   opAt 2732 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2733 (.Dup ⟨0, by decide⟩),
   opAt 2734 .ISZERO,
   pushAt 2735 2 4735,
   opAt 2736 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2906 .JUMPDEST,
   opAt 2907 (.Dup ⟨0, by decide⟩),
   opAt 2908 .MLOAD,
   pushAt 2909 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2910 (.Dup ⟨5, by decide⟩),
   opAt 2911 (.Dup ⟨2, by decide⟩),
   opAt 2912 .MUL,
   opAt 2913 (.Swap ⟨1, by decide⟩),
   opAt 2914 (.Dup ⟨6, by decide⟩),
   opAt 2915 .MULMOD,
   opAt 2916 (.Dup ⟨1, by decide⟩),
   opAt 2917 (.Dup ⟨1, by decide⟩),
   opAt 2918 .LT,
   opAt 2919 .SUB,
   opAt 2920 (.Dup ⟨4, by decide⟩),
   opAt 2921 (.Dup ⟨2, by decide⟩),
   opAt 2922 .ADD,
   opAt 2923 (.Dup ⟨0, by decide⟩),
   opAt 2924 (.Swap ⟨5, by decide⟩),
   opAt 2925 .GT,
   opAt 2926 .SUB,
   opAt 2927 .SUB,
   opAt 2928 (.Dup ⟨3, by decide⟩),
   opAt 2929 (.Dup ⟨3, by decide⟩),
   opAt 2930 .MLOAD,
   opAt 2931 .ADD,
   opAt 2932 (.Dup ⟨0, by decide⟩),
   opAt 2933 (.Swap ⟨4, by decide⟩),
   opAt 2934 .GT,
   opAt 2935 .ADD,
   opAt 2936 (.Swap ⟨2, by decide⟩),
   opAt 2937 (.Dup ⟨2, by decide⟩),
   pushAt 2938 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2939 .ADD,
   opAt 2940 (.Swap ⟨2, by decide⟩),
   opAt 2941 .MSTORE,
   pushAt 2942 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2943 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2944 2 8224,
   opAt 2945 (.Dup ⟨2, by decide⟩),
   opAt 2946 .GT,
   pushAt 2947 2 4952,
   opAt 2948 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2981 .JUMPDEST,
   opAt 2982 (.Dup ⟨0, by decide⟩),
   opAt 2983 .MLOAD,
   opAt 2984 (.Dup ⟨1, by decide⟩),
   pushAt 2985 2 8256,
   opAt 2986 (.Swap ⟨0, by decide⟩),
   opAt 2987 .SUB,
   opAt 2988 .MLOAD,
   opAt 2989 (.Dup ⟨1, by decide⟩),
   opAt 2990 .ADD,
   opAt 2991 (.Dup ⟨0, by decide⟩),
   opAt 2992 (.Dup ⟨2, by decide⟩),
   opAt 2993 .GT,
   opAt 2994 (.Swap ⟨1, by decide⟩),
   opAt 2995 .POP,
   opAt 2996 (.Dup ⟨3, by decide⟩),
   opAt 2997 .ADD,
   opAt 2998 (.Dup ⟨0, by decide⟩),
   opAt 2999 (.Dup ⟨4, by decide⟩),
   opAt 3000 .GT,
   opAt 3001 (.Swap ⟨3, by decide⟩),
   opAt 3002 .POP,
   opAt 3003 (.Dup ⟨2, by decide⟩),
   opAt 3004 .MSTORE,
   opAt 3005 (.Swap ⟨0, by decide⟩),
   opAt 3006 (.Swap ⟨1, by decide⟩),
   opAt 3007 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3008 (.Swap ⟨0, by decide⟩),
   pushAt 3009 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3010 .ADD,
   pushAt 3011 2 8255,
   opAt 3012 (.Dup ⟨1, by decide⟩),
   opAt 3013 .GT,
   pushAt 3014 2 5135,
   opAt 3015 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3037 .JUMPDEST,
   opAt 3038 (.Dup ⟨0, by decide⟩),
   opAt 3039 .MLOAD,
   opAt 3040 (.Dup ⟨1, by decide⟩),
   pushAt 3041 2 8256,
   opAt 3042 (.Swap ⟨0, by decide⟩),
   opAt 3043 .SUB,
   opAt 3044 .MLOAD,
   opAt 3045 (.Dup ⟨1, by decide⟩),
   opAt 3046 (.Dup ⟨1, by decide⟩),
   opAt 3047 .GT,
   opAt 3048 (.Swap ⟨1, by decide⟩),
   opAt 3049 .SUB,
   opAt 3050 (.Dup ⟨3, by decide⟩),
   opAt 3051 (.Dup ⟨1, by decide⟩),
   opAt 3052 .LT,
   opAt 3053 (.Swap ⟨0, by decide⟩),
   opAt 3054 (.Dup ⟨4, by decide⟩),
   opAt 3055 (.Swap ⟨0, by decide⟩),
   opAt 3056 .SUB,
   opAt 3057 (.Dup ⟨3, by decide⟩),
   opAt 3058 .MSTORE,
   opAt 3059 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3060 (.Swap ⟨1, by decide⟩),
   opAt 3061 .POP,
   pushAt 3062 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3063 .ADD,
   pushAt 3064 2 8255,
   opAt 3065 (.Dup ⟨1, by decide⟩),
   opAt 3066 .GT,
   pushAt 3067 2 5241,
   opAt 3068 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
