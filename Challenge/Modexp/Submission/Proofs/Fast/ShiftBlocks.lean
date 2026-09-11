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
  [opAt 2691 .JUMPDEST,
   opAt 2692 (.Dup ⟨0, by decide⟩),
   opAt 2693 .MLOAD,
   opAt 2694 .NOT,
   opAt 2695 (.Dup ⟨2, by decide⟩),
   opAt 2696 .ADD,
   opAt 2697 (.Dup ⟨2, by decide⟩),
   opAt 2698 (.Dup ⟨1, by decide⟩),
   opAt 2699 .LT,
   opAt 2700 (.Swap ⟨2, by decide⟩),
   opAt 2701 .POP,
   opAt 2702 (.Dup ⟨1, by decide⟩),
   pushAt 2703 2 5120,
   opAt 2704 .ADD,
   opAt 2705 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2706 (.Dup ⟨0, by decide⟩),
   opAt 2707 .ISZERO,
   pushAt 2708 2 3583,
   opAt 2709 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2880 .JUMPDEST,
   opAt 2881 (.Dup ⟨0, by decide⟩),
   opAt 2882 .MLOAD,
   pushAt 2883 0 0,
   opAt 2884 .NOT,
   opAt 2885 (.Dup ⟨5, by decide⟩),
   opAt 2886 (.Dup ⟨2, by decide⟩),
   opAt 2887 .MUL,
   opAt 2888 (.Swap ⟨1, by decide⟩),
   opAt 2889 (.Dup ⟨6, by decide⟩),
   opAt 2890 .MULMOD,
   opAt 2891 (.Dup ⟨1, by decide⟩),
   opAt 2892 (.Dup ⟨1, by decide⟩),
   opAt 2893 .LT,
   opAt 2894 .SUB,
   opAt 2895 (.Dup ⟨4, by decide⟩),
   opAt 2896 (.Dup ⟨2, by decide⟩),
   opAt 2897 .ADD,
   opAt 2898 (.Dup ⟨0, by decide⟩),
   opAt 2899 (.Swap ⟨5, by decide⟩),
   opAt 2900 .GT,
   opAt 2901 .SUB,
   opAt 2902 .SUB,
   opAt 2903 (.Dup ⟨3, by decide⟩),
   opAt 2904 (.Dup ⟨3, by decide⟩),
   opAt 2905 .MLOAD,
   opAt 2906 .ADD,
   opAt 2907 (.Dup ⟨0, by decide⟩),
   opAt 2908 (.Swap ⟨4, by decide⟩),
   opAt 2909 .GT,
   opAt 2910 .ADD,
   opAt 2911 (.Swap ⟨2, by decide⟩),
   opAt 2912 (.Dup ⟨2, by decide⟩),
   pushAt 2913 1 31,
   opAt 2914 .NOT,
   opAt 2915 .ADD,
   opAt 2916 (.Swap ⟨2, by decide⟩),
   opAt 2917 .MSTORE,
   pushAt 2918 1 31,
   opAt 2919 .NOT,
   opAt 2920 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2921 2 8224,
   opAt 2922 (.Dup ⟨2, by decide⟩),
   opAt 2923 .GT,
   pushAt 2924 2 3802,
   opAt 2925 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2958 .JUMPDEST,
   opAt 2959 (.Dup ⟨0, by decide⟩),
   opAt 2960 .MLOAD,
   opAt 2961 (.Dup ⟨1, by decide⟩),
   pushAt 2962 2 8256,
   opAt 2963 (.Swap ⟨0, by decide⟩),
   opAt 2964 .SUB,
   opAt 2965 .MLOAD,
   opAt 2966 (.Dup ⟨1, by decide⟩),
   opAt 2967 .ADD,
   opAt 2968 (.Dup ⟨0, by decide⟩),
   opAt 2969 (.Dup ⟨2, by decide⟩),
   opAt 2970 .GT,
   opAt 2971 (.Swap ⟨1, by decide⟩),
   opAt 2972 .POP,
   opAt 2973 (.Dup ⟨3, by decide⟩),
   opAt 2974 .ADD,
   opAt 2975 (.Dup ⟨0, by decide⟩),
   opAt 2976 (.Dup ⟨4, by decide⟩),
   opAt 2977 .GT,
   opAt 2978 (.Swap ⟨3, by decide⟩),
   opAt 2979 .POP,
   opAt 2980 (.Dup ⟨2, by decide⟩),
   opAt 2981 .MSTORE,
   opAt 2982 (.Swap ⟨0, by decide⟩),
   opAt 2983 (.Swap ⟨1, by decide⟩),
   opAt 2984 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2985 (.Swap ⟨0, by decide⟩),
   pushAt 2986 1 31,
   opAt 2987 .NOT,
   opAt 2988 .ADD,
   pushAt 2989 2 8255,
   opAt 2990 (.Dup ⟨1, by decide⟩),
   opAt 2991 .GT,
   pushAt 2992 2 3894,
   opAt 2993 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3015 .JUMPDEST,
   opAt 3016 (.Dup ⟨0, by decide⟩),
   opAt 3017 .MLOAD,
   pushAt 3018 2 8256,
   opAt 3019 (.Dup ⟨2, by decide⟩),
   opAt 3020 .SUB,
   opAt 3021 .MLOAD,
   opAt 3022 (.Dup ⟨1, by decide⟩),
   opAt 3023 (.Dup ⟨1, by decide⟩),
   opAt 3024 .GT,
   opAt 3025 (.Swap ⟨1, by decide⟩),
   opAt 3026 .SUB,
   opAt 3027 (.Dup ⟨3, by decide⟩),
   opAt 3028 (.Dup ⟨1, by decide⟩),
   opAt 3029 .LT,
   opAt 3030 (.Swap ⟨0, by decide⟩),
   opAt 3031 (.Dup ⟨4, by decide⟩),
   opAt 3032 (.Swap ⟨0, by decide⟩),
   opAt 3033 .SUB,
   opAt 3034 (.Dup ⟨3, by decide⟩),
   opAt 3035 .MSTORE,
   opAt 3036 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3037 (.Swap ⟨1, by decide⟩),
   opAt 3038 .POP,
   pushAt 3039 1 31,
   opAt 3040 .NOT,
   opAt 3041 .ADD,
   pushAt 3042 2 8255,
   opAt 3043 (.Dup ⟨1, by decide⟩),
   opAt 3044 .GT,
   pushAt 3045 2 3970,
   opAt 3046 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
