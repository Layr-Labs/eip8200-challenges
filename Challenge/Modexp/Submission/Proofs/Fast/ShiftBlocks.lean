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
  [opAt 2709 .JUMPDEST,
   opAt 2710 (.Dup ⟨0, by decide⟩),
   opAt 2711 .MLOAD,
   opAt 2712 .NOT,
   opAt 2713 (.Dup ⟨2, by decide⟩),
   opAt 2714 .ADD,
   opAt 2715 (.Dup ⟨2, by decide⟩),
   opAt 2716 (.Dup ⟨1, by decide⟩),
   opAt 2717 .LT,
   opAt 2718 (.Swap ⟨2, by decide⟩),
   opAt 2719 .POP,
   opAt 2720 (.Dup ⟨1, by decide⟩),
   pushAt 2721 2 5120,
   opAt 2722 .ADD,
   opAt 2723 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2724 (.Dup ⟨0, by decide⟩),
   opAt 2725 .ISZERO,
   pushAt 2726 2 4735,
   opAt 2727 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2897 .JUMPDEST,
   opAt 2898 (.Dup ⟨0, by decide⟩),
   opAt 2899 .MLOAD,
   pushAt 2900 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2901 (.Dup ⟨5, by decide⟩),
   opAt 2902 (.Dup ⟨2, by decide⟩),
   opAt 2903 .MUL,
   opAt 2904 (.Swap ⟨1, by decide⟩),
   opAt 2905 (.Dup ⟨6, by decide⟩),
   opAt 2906 .MULMOD,
   opAt 2907 (.Dup ⟨1, by decide⟩),
   opAt 2908 (.Dup ⟨1, by decide⟩),
   opAt 2909 .LT,
   opAt 2910 .SUB,
   opAt 2911 (.Dup ⟨4, by decide⟩),
   opAt 2912 (.Dup ⟨2, by decide⟩),
   opAt 2913 .ADD,
   opAt 2914 (.Dup ⟨0, by decide⟩),
   opAt 2915 (.Swap ⟨5, by decide⟩),
   opAt 2916 .GT,
   opAt 2917 .SUB,
   opAt 2918 .SUB,
   opAt 2919 (.Dup ⟨3, by decide⟩),
   opAt 2920 (.Dup ⟨3, by decide⟩),
   opAt 2921 .MLOAD,
   opAt 2922 .ADD,
   opAt 2923 (.Dup ⟨0, by decide⟩),
   opAt 2924 (.Swap ⟨4, by decide⟩),
   opAt 2925 .GT,
   opAt 2926 .ADD,
   opAt 2927 (.Swap ⟨2, by decide⟩),
   opAt 2928 (.Dup ⟨2, by decide⟩),
   pushAt 2929 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2930 .ADD,
   opAt 2931 (.Swap ⟨2, by decide⟩),
   opAt 2932 .MSTORE,
   pushAt 2933 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2934 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2935 2 8224,
   opAt 2936 (.Dup ⟨2, by decide⟩),
   opAt 2937 .GT,
   pushAt 2938 2 4952,
   opAt 2939 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2972 .JUMPDEST,
   opAt 2973 (.Dup ⟨0, by decide⟩),
   opAt 2974 .MLOAD,
   opAt 2975 (.Dup ⟨1, by decide⟩),
   pushAt 2976 2 8256,
   opAt 2977 (.Swap ⟨0, by decide⟩),
   opAt 2978 .SUB,
   opAt 2979 .MLOAD,
   opAt 2980 (.Dup ⟨1, by decide⟩),
   opAt 2981 .ADD,
   opAt 2982 (.Dup ⟨0, by decide⟩),
   opAt 2983 (.Dup ⟨2, by decide⟩),
   opAt 2984 .GT,
   opAt 2985 (.Swap ⟨1, by decide⟩),
   opAt 2986 .POP,
   opAt 2987 (.Dup ⟨3, by decide⟩),
   opAt 2988 .ADD,
   opAt 2989 (.Dup ⟨0, by decide⟩),
   opAt 2990 (.Dup ⟨4, by decide⟩),
   opAt 2991 .GT,
   opAt 2992 (.Swap ⟨3, by decide⟩),
   opAt 2993 .POP,
   opAt 2994 (.Dup ⟨2, by decide⟩),
   opAt 2995 .MSTORE,
   opAt 2996 (.Swap ⟨0, by decide⟩),
   opAt 2997 (.Swap ⟨1, by decide⟩),
   opAt 2998 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2999 (.Swap ⟨0, by decide⟩),
   pushAt 3000 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3001 .ADD,
   pushAt 3002 2 8255,
   opAt 3003 (.Dup ⟨1, by decide⟩),
   opAt 3004 .GT,
   pushAt 3005 2 5135,
   opAt 3006 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3028 .JUMPDEST,
   opAt 3029 (.Dup ⟨0, by decide⟩),
   opAt 3030 .MLOAD,
   opAt 3031 (.Dup ⟨1, by decide⟩),
   pushAt 3032 2 8256,
   opAt 3033 (.Swap ⟨0, by decide⟩),
   opAt 3034 .SUB,
   opAt 3035 .MLOAD,
   opAt 3036 (.Dup ⟨1, by decide⟩),
   opAt 3037 (.Dup ⟨1, by decide⟩),
   opAt 3038 .GT,
   opAt 3039 (.Swap ⟨1, by decide⟩),
   opAt 3040 .SUB,
   opAt 3041 (.Dup ⟨3, by decide⟩),
   opAt 3042 (.Dup ⟨1, by decide⟩),
   opAt 3043 .LT,
   opAt 3044 (.Swap ⟨0, by decide⟩),
   opAt 3045 (.Dup ⟨4, by decide⟩),
   opAt 3046 (.Swap ⟨0, by decide⟩),
   opAt 3047 .SUB,
   opAt 3048 (.Dup ⟨3, by decide⟩),
   opAt 3049 .MSTORE,
   opAt 3050 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3051 (.Swap ⟨1, by decide⟩),
   opAt 3052 .POP,
   pushAt 3053 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3054 .ADD,
   pushAt 3055 2 8255,
   opAt 3056 (.Dup ⟨1, by decide⟩),
   opAt 3057 .GT,
   pushAt 3058 2 5241,
   opAt 3059 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
