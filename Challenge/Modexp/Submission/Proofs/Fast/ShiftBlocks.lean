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
  [opAt 2710 .JUMPDEST,
   opAt 2711 (.Dup ⟨0, by decide⟩),
   opAt 2712 .MLOAD,
   opAt 2713 .NOT,
   opAt 2714 (.Dup ⟨2, by decide⟩),
   opAt 2715 .ADD,
   opAt 2716 (.Dup ⟨2, by decide⟩),
   opAt 2717 (.Dup ⟨1, by decide⟩),
   opAt 2718 .LT,
   opAt 2719 (.Swap ⟨2, by decide⟩),
   opAt 2720 .POP,
   opAt 2721 (.Dup ⟨1, by decide⟩),
   pushAt 2722 2 5120,
   opAt 2723 .ADD,
   opAt 2724 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2725 (.Dup ⟨0, by decide⟩),
   opAt 2726 .ISZERO,
   pushAt 2727 2 4735,
   opAt 2728 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2898 .JUMPDEST,
   opAt 2899 (.Dup ⟨0, by decide⟩),
   opAt 2900 .MLOAD,
   pushAt 2901 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2902 (.Dup ⟨5, by decide⟩),
   opAt 2903 (.Dup ⟨2, by decide⟩),
   opAt 2904 .MUL,
   opAt 2905 (.Swap ⟨1, by decide⟩),
   opAt 2906 (.Dup ⟨6, by decide⟩),
   opAt 2907 .MULMOD,
   opAt 2908 (.Dup ⟨1, by decide⟩),
   opAt 2909 (.Dup ⟨1, by decide⟩),
   opAt 2910 .LT,
   opAt 2911 .SUB,
   opAt 2912 (.Dup ⟨4, by decide⟩),
   opAt 2913 (.Dup ⟨2, by decide⟩),
   opAt 2914 .ADD,
   opAt 2915 (.Dup ⟨0, by decide⟩),
   opAt 2916 (.Swap ⟨5, by decide⟩),
   opAt 2917 .GT,
   opAt 2918 .SUB,
   opAt 2919 .SUB,
   opAt 2920 (.Dup ⟨3, by decide⟩),
   opAt 2921 (.Dup ⟨3, by decide⟩),
   opAt 2922 .MLOAD,
   opAt 2923 .ADD,
   opAt 2924 (.Dup ⟨0, by decide⟩),
   opAt 2925 (.Swap ⟨4, by decide⟩),
   opAt 2926 .GT,
   opAt 2927 .ADD,
   opAt 2928 (.Swap ⟨2, by decide⟩),
   opAt 2929 (.Dup ⟨2, by decide⟩),
   pushAt 2930 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2931 .ADD,
   opAt 2932 (.Swap ⟨2, by decide⟩),
   opAt 2933 .MSTORE,
   pushAt 2934 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2935 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2936 2 8224,
   opAt 2937 (.Dup ⟨2, by decide⟩),
   opAt 2938 .GT,
   pushAt 2939 2 4952,
   opAt 2940 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2973 .JUMPDEST,
   opAt 2974 (.Dup ⟨0, by decide⟩),
   opAt 2975 .MLOAD,
   opAt 2976 (.Dup ⟨1, by decide⟩),
   pushAt 2977 2 8256,
   opAt 2978 (.Swap ⟨0, by decide⟩),
   opAt 2979 .SUB,
   opAt 2980 .MLOAD,
   opAt 2981 (.Dup ⟨1, by decide⟩),
   opAt 2982 .ADD,
   opAt 2983 (.Dup ⟨0, by decide⟩),
   opAt 2984 (.Dup ⟨2, by decide⟩),
   opAt 2985 .GT,
   opAt 2986 (.Swap ⟨1, by decide⟩),
   opAt 2987 .POP,
   opAt 2988 (.Dup ⟨3, by decide⟩),
   opAt 2989 .ADD,
   opAt 2990 (.Dup ⟨0, by decide⟩),
   opAt 2991 (.Dup ⟨4, by decide⟩),
   opAt 2992 .GT,
   opAt 2993 (.Swap ⟨3, by decide⟩),
   opAt 2994 .POP,
   opAt 2995 (.Dup ⟨2, by decide⟩),
   opAt 2996 .MSTORE,
   opAt 2997 (.Swap ⟨0, by decide⟩),
   opAt 2998 (.Swap ⟨1, by decide⟩),
   opAt 2999 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3000 (.Swap ⟨0, by decide⟩),
   pushAt 3001 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3002 .ADD,
   pushAt 3003 2 8255,
   opAt 3004 (.Dup ⟨1, by decide⟩),
   opAt 3005 .GT,
   pushAt 3006 2 5135,
   opAt 3007 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3029 .JUMPDEST,
   opAt 3030 (.Dup ⟨0, by decide⟩),
   opAt 3031 .MLOAD,
   opAt 3032 (.Dup ⟨1, by decide⟩),
   pushAt 3033 2 8256,
   opAt 3034 (.Swap ⟨0, by decide⟩),
   opAt 3035 .SUB,
   opAt 3036 .MLOAD,
   opAt 3037 (.Dup ⟨1, by decide⟩),
   opAt 3038 (.Dup ⟨1, by decide⟩),
   opAt 3039 .GT,
   opAt 3040 (.Swap ⟨1, by decide⟩),
   opAt 3041 .SUB,
   opAt 3042 (.Dup ⟨3, by decide⟩),
   opAt 3043 (.Dup ⟨1, by decide⟩),
   opAt 3044 .LT,
   opAt 3045 (.Swap ⟨0, by decide⟩),
   opAt 3046 (.Dup ⟨4, by decide⟩),
   opAt 3047 (.Swap ⟨0, by decide⟩),
   opAt 3048 .SUB,
   opAt 3049 (.Dup ⟨3, by decide⟩),
   opAt 3050 .MSTORE,
   opAt 3051 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3052 (.Swap ⟨1, by decide⟩),
   opAt 3053 .POP,
   pushAt 3054 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3055 .ADD,
   pushAt 3056 2 8255,
   opAt 3057 (.Dup ⟨1, by decide⟩),
   opAt 3058 .GT,
   pushAt 3059 2 5241,
   opAt 3060 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
