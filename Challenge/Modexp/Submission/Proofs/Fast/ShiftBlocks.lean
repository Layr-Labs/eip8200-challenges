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
   pushAt 2881 2 3837,
   opAt 2882 .JUMP,
   opAt 2897 .JUMPDEST,
   opAt 2898 (.Dup ⟨5, by decide⟩),
   opAt 2899 (.Dup ⟨2, by decide⟩),
   opAt 2900 .MUL,
   opAt 2901 (.Swap ⟨1, by decide⟩),
   opAt 2902 (.Dup ⟨6, by decide⟩),
   opAt 2903 .MULMOD,
   opAt 2904 (.Dup ⟨1, by decide⟩),
   opAt 2905 (.Dup ⟨1, by decide⟩),
   opAt 2906 .LT,
   opAt 2907 .SUB,
   opAt 2908 (.Dup ⟨4, by decide⟩),
   opAt 2909 (.Dup ⟨2, by decide⟩),
   opAt 2910 .ADD,
   opAt 2911 (.Dup ⟨0, by decide⟩),
   opAt 2912 (.Swap ⟨5, by decide⟩),
   opAt 2913 .GT,
   opAt 2914 .SUB,
   opAt 2915 .SUB,
   opAt 2916 (.Dup ⟨3, by decide⟩),
   opAt 2917 (.Dup ⟨3, by decide⟩),
   opAt 2918 .MLOAD,
   opAt 2919 .ADD,
   opAt 2920 (.Dup ⟨0, by decide⟩),
   opAt 2921 (.Swap ⟨4, by decide⟩),
   opAt 2922 .GT,
   opAt 2923 .ADD,
   opAt 2924 (.Swap ⟨2, by decide⟩),
   opAt 2925 (.Dup ⟨2, by decide⟩),
   pushAt 2926 5 31,
   opAt 2927 .NOT,
   pushAt 2928 2 3898,
   opAt 2929 .JUMP,
   opAt 2944 .JUMPDEST,
   opAt 2945 .ADD,
   opAt 2946 (.Swap ⟨2, by decide⟩),
   opAt 2947 .MSTORE,
   pushAt 2948 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2949 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2950 2 8224,
   opAt 2951 (.Dup ⟨2, by decide⟩),
   opAt 2952 .GT,
   pushAt 2953 2 3802,
   opAt 2954 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2987 .JUMPDEST,
   opAt 2988 (.Dup ⟨0, by decide⟩),
   opAt 2989 .MLOAD,
   opAt 2990 (.Dup ⟨1, by decide⟩),
   pushAt 2991 2 8256,
   opAt 2992 (.Swap ⟨0, by decide⟩),
   opAt 2993 .SUB,
   opAt 2994 .MLOAD,
   opAt 2995 (.Dup ⟨1, by decide⟩),
   opAt 2996 .ADD,
   opAt 2997 (.Dup ⟨0, by decide⟩),
   opAt 2998 (.Dup ⟨2, by decide⟩),
   opAt 2999 .GT,
   opAt 3000 (.Swap ⟨1, by decide⟩),
   opAt 3001 .POP,
   opAt 3002 (.Dup ⟨3, by decide⟩),
   opAt 3003 .ADD,
   opAt 3004 (.Dup ⟨0, by decide⟩),
   opAt 3005 (.Dup ⟨4, by decide⟩),
   opAt 3006 .GT,
   opAt 3007 (.Swap ⟨3, by decide⟩),
   opAt 3008 .POP,
   opAt 3009 (.Dup ⟨2, by decide⟩),
   opAt 3010 .MSTORE,
   opAt 3011 (.Swap ⟨0, by decide⟩),
   opAt 3012 (.Swap ⟨1, by decide⟩),
   opAt 3013 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3014 (.Swap ⟨0, by decide⟩),
   pushAt 3015 1 31,
   opAt 3016 .NOT,
   opAt 3017 .ADD,
   pushAt 3018 2 8255,
   opAt 3019 (.Dup ⟨1, by decide⟩),
   opAt 3020 .GT,
   pushAt 3021 2 3985,
   opAt 3022 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3044 .JUMPDEST,
   opAt 3045 (.Dup ⟨0, by decide⟩),
   opAt 3046 .MLOAD,
   pushAt 3047 2 8256,
   opAt 3048 (.Dup ⟨2, by decide⟩),
   opAt 3049 .SUB,
   opAt 3050 .MLOAD,
   opAt 3051 (.Dup ⟨1, by decide⟩),
   opAt 3052 (.Dup ⟨1, by decide⟩),
   opAt 3053 .GT,
   opAt 3054 (.Swap ⟨1, by decide⟩),
   opAt 3055 .SUB,
   opAt 3056 (.Dup ⟨3, by decide⟩),
   opAt 3057 (.Dup ⟨1, by decide⟩),
   opAt 3058 .LT,
   opAt 3059 (.Swap ⟨0, by decide⟩),
   opAt 3060 (.Dup ⟨4, by decide⟩),
   opAt 3061 (.Swap ⟨0, by decide⟩),
   opAt 3062 .SUB,
   opAt 3063 (.Dup ⟨3, by decide⟩),
   opAt 3064 .MSTORE,
   opAt 3065 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3066 (.Swap ⟨1, by decide⟩),
   opAt 3067 .POP,
   pushAt 3068 1 31,
   opAt 3069 .NOT,
   opAt 3070 .ADD,
   pushAt 3071 2 8255,
   opAt 3072 (.Dup ⟨1, by decide⟩),
   opAt 3073 .GT,
   pushAt 3074 2 4061,
   opAt 3075 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
