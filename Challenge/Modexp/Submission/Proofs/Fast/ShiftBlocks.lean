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
  [opAt 2689 .JUMPDEST,
   opAt 2690 (.Dup ⟨0, by decide⟩),
   opAt 2691 .MLOAD,
   opAt 2692 .NOT,
   opAt 2693 (.Dup ⟨2, by decide⟩),
   opAt 2694 .ADD,
   opAt 2695 (.Dup ⟨2, by decide⟩),
   opAt 2696 (.Dup ⟨1, by decide⟩),
   opAt 2697 .LT,
   opAt 2698 (.Swap ⟨2, by decide⟩),
   opAt 2699 .POP,
   opAt 2700 (.Dup ⟨1, by decide⟩),
   pushAt 2701 2 5120,
   opAt 2702 .ADD,
   opAt 2703 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2704 (.Dup ⟨0, by decide⟩),
   opAt 2705 .ISZERO,
   pushAt 2706 2 3583,
   opAt 2707 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..38). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2882 .JUMPDEST,
   opAt 2883 (.Dup ⟨0, by decide⟩),
   opAt 2884 .MLOAD,
   pushAt 2885 0 0,
   opAt 2886 .NOT,
   opAt 2887 (.Dup ⟨6, by decide⟩),
   opAt 2888 (.Dup ⟨2, by decide⟩),
   opAt 2889 .MUL,
   opAt 2890 (.Swap ⟨1, by decide⟩),
   opAt 2891 (.Dup ⟨7, by decide⟩),
   opAt 2892 .MULMOD,
   opAt 2893 (.Dup ⟨1, by decide⟩),
   opAt 2894 (.Dup ⟨1, by decide⟩),
   opAt 2895 .LT,
   opAt 2896 .SUB,
   opAt 2897 (.Dup ⟨5, by decide⟩),
   opAt 2898 (.Dup ⟨2, by decide⟩),
   opAt 2899 .ADD,
   opAt 2900 (.Dup ⟨0, by decide⟩),
   opAt 2901 (.Swap ⟨6, by decide⟩),
   opAt 2902 .GT,
   opAt 2903 .SUB,
   opAt 2904 .SUB,
   opAt 2905 (.Dup ⟨4, by decide⟩),
   opAt 2906 (.Dup ⟨3, by decide⟩),
   opAt 2907 .MLOAD,
   opAt 2908 .ADD,
   opAt 2909 (.Dup ⟨0, by decide⟩),
   opAt 2910 (.Swap ⟨5, by decide⟩),
   opAt 2911 .GT,
   opAt 2912 .ADD,
   opAt 2913 (.Swap ⟨3, by decide⟩),
   opAt 2914 (.Dup ⟨2, by decide⟩),
   opAt 2915 (.Dup ⟨4, by decide⟩),
   opAt 2916 .ADD,
   opAt 2917 (.Swap ⟨2, by decide⟩),
   opAt 2918 .MSTORE,
   opAt 2919 (.Dup ⟨2, by decide⟩),
   opAt 2920 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 39..43). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2921 2 8224,
   opAt 2922 (.Dup ⟨2, by decide⟩),
   opAt 2923 .GT,
   pushAt 2924 2 3809,
   opAt 2925 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2959 .JUMPDEST,
   opAt 2960 (.Dup ⟨0, by decide⟩),
   opAt 2961 .MLOAD,
   opAt 2962 (.Dup ⟨1, by decide⟩),
   pushAt 2963 2 8256,
   opAt 2964 (.Swap ⟨0, by decide⟩),
   opAt 2965 .SUB,
   opAt 2966 .MLOAD,
   opAt 2967 (.Dup ⟨1, by decide⟩),
   opAt 2968 .ADD,
   opAt 2969 (.Dup ⟨0, by decide⟩),
   opAt 2970 (.Dup ⟨2, by decide⟩),
   opAt 2971 .GT,
   opAt 2972 (.Swap ⟨1, by decide⟩),
   opAt 2973 .POP,
   opAt 2974 (.Dup ⟨3, by decide⟩),
   opAt 2975 .ADD,
   opAt 2976 (.Dup ⟨0, by decide⟩),
   opAt 2977 (.Dup ⟨4, by decide⟩),
   opAt 2978 .GT,
   opAt 2979 (.Swap ⟨3, by decide⟩),
   opAt 2980 .POP,
   opAt 2981 (.Dup ⟨2, by decide⟩),
   opAt 2982 .MSTORE,
   opAt 2983 (.Swap ⟨0, by decide⟩),
   opAt 2984 (.Swap ⟨1, by decide⟩),
   opAt 2985 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2986 (.Swap ⟨0, by decide⟩),
   pushAt 2987 1 31,
   opAt 2988 .NOT,
   opAt 2989 .ADD,
   pushAt 2990 2 8255,
   opAt 2991 (.Dup ⟨1, by decide⟩),
   opAt 2992 .GT,
   pushAt 2993 2 3898,
   opAt 2994 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3016 .JUMPDEST,
   opAt 3017 (.Dup ⟨0, by decide⟩),
   opAt 3018 .MLOAD,
   pushAt 3019 2 8256,
   opAt 3020 (.Dup ⟨2, by decide⟩),
   opAt 3021 .SUB,
   opAt 3022 .MLOAD,
   opAt 3023 (.Dup ⟨1, by decide⟩),
   opAt 3024 (.Dup ⟨1, by decide⟩),
   opAt 3025 .GT,
   opAt 3026 (.Swap ⟨1, by decide⟩),
   opAt 3027 .SUB,
   opAt 3028 (.Dup ⟨3, by decide⟩),
   opAt 3029 (.Dup ⟨1, by decide⟩),
   opAt 3030 .LT,
   opAt 3031 (.Swap ⟨0, by decide⟩),
   opAt 3032 (.Dup ⟨4, by decide⟩),
   opAt 3033 (.Swap ⟨0, by decide⟩),
   opAt 3034 .SUB,
   opAt 3035 (.Dup ⟨3, by decide⟩),
   opAt 3036 .MSTORE,
   opAt 3037 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3038 (.Swap ⟨1, by decide⟩),
   opAt 3039 .POP,
   pushAt 3040 1 31,
   opAt 3041 .NOT,
   opAt 3042 .ADD,
   pushAt 3043 2 8255,
   opAt 3044 (.Dup ⟨1, by decide⟩),
   opAt 3045 .GT,
   pushAt 3046 2 3974,
   opAt 3047 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
