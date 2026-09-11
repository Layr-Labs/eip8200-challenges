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
  [opAt 2880 .JUMPDEST,
   opAt 2881 (.Dup ⟨0, by decide⟩),
   opAt 2882 .MLOAD,
   pushAt 2883 0 0,
   opAt 2884 .NOT,
   opAt 2885 (.Dup ⟨6, by decide⟩),
   opAt 2886 (.Dup ⟨2, by decide⟩),
   opAt 2887 .MUL,
   opAt 2888 (.Swap ⟨1, by decide⟩),
   opAt 2889 (.Dup ⟨7, by decide⟩),
   opAt 2890 .MULMOD,
   opAt 2891 (.Dup ⟨1, by decide⟩),
   opAt 2892 (.Dup ⟨1, by decide⟩),
   opAt 2893 .LT,
   opAt 2894 .SUB,
   opAt 2895 (.Dup ⟨5, by decide⟩),
   opAt 2896 (.Dup ⟨2, by decide⟩),
   opAt 2897 .ADD,
   opAt 2898 (.Dup ⟨0, by decide⟩),
   opAt 2899 (.Swap ⟨6, by decide⟩),
   opAt 2900 .GT,
   opAt 2901 .SUB,
   opAt 2902 .SUB,
   opAt 2903 (.Dup ⟨4, by decide⟩),
   opAt 2904 (.Dup ⟨3, by decide⟩),
   opAt 2905 .MLOAD,
   opAt 2906 .ADD,
   opAt 2907 (.Dup ⟨0, by decide⟩),
   opAt 2908 (.Swap ⟨5, by decide⟩),
   opAt 2909 .GT,
   opAt 2910 .ADD,
   opAt 2911 (.Swap ⟨3, by decide⟩),
   opAt 2912 (.Dup ⟨2, by decide⟩),
   opAt 2913 (.Dup ⟨4, by decide⟩),
   opAt 2914 .ADD,
   opAt 2915 (.Swap ⟨2, by decide⟩),
   opAt 2916 .MSTORE,
   opAt 2917 (.Dup ⟨2, by decide⟩),
   opAt 2918 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 39..43). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2919 2 8224,
   opAt 2920 (.Dup ⟨2, by decide⟩),
   opAt 2921 .GT,
   pushAt 2922 2 3805,
   opAt 2923 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2957 .JUMPDEST,
   opAt 2958 (.Dup ⟨0, by decide⟩),
   opAt 2959 .MLOAD,
   opAt 2960 (.Dup ⟨1, by decide⟩),
   pushAt 2961 2 8256,
   opAt 2962 (.Swap ⟨0, by decide⟩),
   opAt 2963 .SUB,
   opAt 2964 .MLOAD,
   opAt 2965 (.Dup ⟨1, by decide⟩),
   opAt 2966 .ADD,
   opAt 2967 (.Dup ⟨0, by decide⟩),
   opAt 2968 (.Dup ⟨2, by decide⟩),
   opAt 2969 .GT,
   opAt 2970 (.Swap ⟨1, by decide⟩),
   opAt 2971 .POP,
   opAt 2972 (.Dup ⟨3, by decide⟩),
   opAt 2973 .ADD,
   opAt 2974 (.Dup ⟨0, by decide⟩),
   opAt 2975 (.Dup ⟨4, by decide⟩),
   opAt 2976 .GT,
   opAt 2977 (.Swap ⟨3, by decide⟩),
   opAt 2978 .POP,
   opAt 2979 (.Dup ⟨2, by decide⟩),
   opAt 2980 .MSTORE,
   opAt 2981 (.Swap ⟨0, by decide⟩),
   opAt 2982 (.Swap ⟨1, by decide⟩),
   opAt 2983 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2984 (.Swap ⟨0, by decide⟩),
   pushAt 2985 1 31,
   opAt 2986 .NOT,
   opAt 2987 .ADD,
   pushAt 2988 2 8255,
   opAt 2989 (.Dup ⟨1, by decide⟩),
   opAt 2990 .GT,
   pushAt 2991 2 3894,
   opAt 2992 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3014 .JUMPDEST,
   opAt 3015 (.Dup ⟨0, by decide⟩),
   opAt 3016 .MLOAD,
   pushAt 3017 2 8256,
   opAt 3018 (.Dup ⟨2, by decide⟩),
   opAt 3019 .SUB,
   opAt 3020 .MLOAD,
   opAt 3021 (.Dup ⟨1, by decide⟩),
   opAt 3022 (.Dup ⟨1, by decide⟩),
   opAt 3023 .GT,
   opAt 3024 (.Swap ⟨1, by decide⟩),
   opAt 3025 .SUB,
   opAt 3026 (.Dup ⟨3, by decide⟩),
   opAt 3027 (.Dup ⟨1, by decide⟩),
   opAt 3028 .LT,
   opAt 3029 (.Swap ⟨0, by decide⟩),
   opAt 3030 (.Dup ⟨4, by decide⟩),
   opAt 3031 (.Swap ⟨0, by decide⟩),
   opAt 3032 .SUB,
   opAt 3033 (.Dup ⟨3, by decide⟩),
   opAt 3034 .MSTORE,
   opAt 3035 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3036 (.Swap ⟨1, by decide⟩),
   opAt 3037 .POP,
   pushAt 3038 1 31,
   opAt 3039 .NOT,
   opAt 3040 .ADD,
   pushAt 3041 2 8255,
   opAt 3042 (.Dup ⟨1, by decide⟩),
   opAt 3043 .GT,
   pushAt 3044 2 3970,
   opAt 3045 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
