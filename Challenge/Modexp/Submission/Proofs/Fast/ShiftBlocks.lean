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
  [opAt 2687 .JUMPDEST,
   opAt 2688 (.Dup ⟨0, by decide⟩),
   opAt 2689 .MLOAD,
   opAt 2690 .NOT,
   opAt 2691 (.Dup ⟨2, by decide⟩),
   opAt 2692 .ADD,
   opAt 2693 (.Dup ⟨2, by decide⟩),
   opAt 2694 (.Dup ⟨1, by decide⟩),
   opAt 2695 .LT,
   opAt 2696 (.Swap ⟨2, by decide⟩),
   opAt 2697 .POP,
   opAt 2698 (.Dup ⟨1, by decide⟩),
   pushAt 2699 2 5120,
   opAt 2700 .ADD,
   opAt 2701 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2702 (.Dup ⟨0, by decide⟩),
   opAt 2703 .ISZERO,
   pushAt 2704 2 3583,
   opAt 2705 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2876 .JUMPDEST,
   opAt 2877 (.Dup ⟨0, by decide⟩),
   opAt 2878 .MLOAD,
   pushAt 2879 0 0,
   opAt 2880 .NOT,
   opAt 2881 .JUMPDEST,
   opAt 2882 (.Dup ⟨5, by decide⟩),
   opAt 2883 (.Dup ⟨2, by decide⟩),
   opAt 2884 .MUL,
   opAt 2885 (.Swap ⟨1, by decide⟩),
   opAt 2886 (.Dup ⟨6, by decide⟩),
   opAt 2887 .MULMOD,
   opAt 2888 (.Dup ⟨1, by decide⟩),
   opAt 2889 (.Dup ⟨1, by decide⟩),
   opAt 2890 .LT,
   opAt 2891 .SUB,
   opAt 2892 (.Dup ⟨4, by decide⟩),
   opAt 2893 (.Dup ⟨2, by decide⟩),
   opAt 2894 .ADD,
   opAt 2895 (.Dup ⟨0, by decide⟩),
   opAt 2896 (.Swap ⟨5, by decide⟩),
   opAt 2897 .GT,
   opAt 2898 .SUB,
   opAt 2899 .SUB,
   opAt 2900 (.Dup ⟨3, by decide⟩),
   opAt 2901 (.Dup ⟨3, by decide⟩),
   opAt 2902 .MLOAD,
   opAt 2903 .ADD,
   opAt 2904 (.Dup ⟨0, by decide⟩),
   opAt 2905 (.Swap ⟨4, by decide⟩),
   opAt 2906 .GT,
   opAt 2907 .ADD,
   opAt 2908 (.Swap ⟨2, by decide⟩),
   opAt 2909 (.Dup ⟨2, by decide⟩),
   pushAt 2910 5 31,
   opAt 2911 .NOT,
   pushAt 2912 2 3898,
   opAt 2913 .JUMP,
   opAt 2946 .JUMPDEST,
   opAt 2947 .ADD,
   opAt 2948 (.Swap ⟨2, by decide⟩),
   opAt 2949 .MSTORE,
   pushAt 2950 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2951 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2952 2 8224,
   opAt 2953 (.Dup ⟨2, by decide⟩),
   opAt 2954 .GT,
   pushAt 2955 2 3802,
   opAt 2956 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2989 .JUMPDEST,
   opAt 2990 (.Dup ⟨0, by decide⟩),
   opAt 2991 .MLOAD,
   opAt 2992 (.Dup ⟨1, by decide⟩),
   pushAt 2993 2 8256,
   opAt 2994 (.Swap ⟨0, by decide⟩),
   opAt 2995 .SUB,
   opAt 2996 .MLOAD,
   opAt 2997 (.Dup ⟨1, by decide⟩),
   opAt 2998 .ADD,
   opAt 2999 (.Dup ⟨0, by decide⟩),
   opAt 3000 (.Dup ⟨2, by decide⟩),
   opAt 3001 .GT,
   opAt 3002 (.Swap ⟨1, by decide⟩),
   opAt 3003 .POP,
   opAt 3004 (.Dup ⟨3, by decide⟩),
   opAt 3005 .ADD,
   opAt 3006 (.Dup ⟨0, by decide⟩),
   opAt 3007 (.Dup ⟨4, by decide⟩),
   opAt 3008 .GT,
   opAt 3009 (.Swap ⟨3, by decide⟩),
   opAt 3010 .POP,
   opAt 3011 (.Dup ⟨2, by decide⟩),
   opAt 3012 .MSTORE,
   opAt 3013 (.Swap ⟨0, by decide⟩),
   opAt 3014 (.Swap ⟨1, by decide⟩),
   opAt 3015 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3016 (.Swap ⟨0, by decide⟩),
   pushAt 3017 1 31,
   opAt 3018 .NOT,
   opAt 3019 .ADD,
   pushAt 3020 2 8255,
   opAt 3021 (.Dup ⟨1, by decide⟩),
   opAt 3022 .GT,
   pushAt 3023 2 3985,
   opAt 3024 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3046 .JUMPDEST,
   opAt 3047 (.Dup ⟨0, by decide⟩),
   opAt 3048 .MLOAD,
   pushAt 3049 2 8256,
   opAt 3050 (.Dup ⟨2, by decide⟩),
   opAt 3051 .SUB,
   opAt 3052 .MLOAD,
   opAt 3053 (.Dup ⟨1, by decide⟩),
   opAt 3054 (.Dup ⟨1, by decide⟩),
   opAt 3055 .GT,
   opAt 3056 (.Swap ⟨1, by decide⟩),
   opAt 3057 .SUB,
   opAt 3058 (.Dup ⟨3, by decide⟩),
   opAt 3059 (.Dup ⟨1, by decide⟩),
   opAt 3060 .LT,
   opAt 3061 (.Swap ⟨0, by decide⟩),
   opAt 3062 (.Dup ⟨4, by decide⟩),
   opAt 3063 (.Swap ⟨0, by decide⟩),
   opAt 3064 .SUB,
   opAt 3065 (.Dup ⟨3, by decide⟩),
   opAt 3066 .MSTORE,
   opAt 3067 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3068 (.Swap ⟨1, by decide⟩),
   opAt 3069 .POP,
   pushAt 3070 1 31,
   opAt 3071 .NOT,
   opAt 3072 .ADD,
   pushAt 3073 2 8255,
   opAt 3074 (.Dup ⟨1, by decide⟩),
   opAt 3075 .GT,
   pushAt 3076 2 4061,
   opAt 3077 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
