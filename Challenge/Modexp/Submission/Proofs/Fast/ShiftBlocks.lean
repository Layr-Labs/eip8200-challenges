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
   pushAt 2879 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2880 (.Dup ⟨5, by decide⟩),
   opAt 2881 (.Dup ⟨2, by decide⟩),
   opAt 2882 .MUL,
   opAt 2883 (.Swap ⟨1, by decide⟩),
   opAt 2884 (.Dup ⟨6, by decide⟩),
   opAt 2885 .MULMOD,
   opAt 2886 (.Dup ⟨1, by decide⟩),
   opAt 2887 (.Dup ⟨1, by decide⟩),
   opAt 2888 .LT,
   opAt 2889 .SUB,
   opAt 2890 (.Dup ⟨4, by decide⟩),
   opAt 2891 (.Dup ⟨2, by decide⟩),
   opAt 2892 .ADD,
   opAt 2893 (.Dup ⟨0, by decide⟩),
   opAt 2894 (.Swap ⟨5, by decide⟩),
   opAt 2895 .GT,
   opAt 2896 .SUB,
   opAt 2897 .SUB,
   opAt 2898 (.Dup ⟨3, by decide⟩),
   opAt 2899 (.Dup ⟨3, by decide⟩),
   opAt 2900 .MLOAD,
   opAt 2901 .ADD,
   opAt 2902 (.Dup ⟨0, by decide⟩),
   opAt 2903 (.Swap ⟨4, by decide⟩),
   opAt 2904 .GT,
   opAt 2905 .ADD,
   opAt 2906 (.Swap ⟨2, by decide⟩),
   opAt 2907 (.Dup ⟨2, by decide⟩),
   pushAt 2908 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2909 .ADD,
   opAt 2910 (.Swap ⟨2, by decide⟩),
   opAt 2911 .MSTORE,
   pushAt 2912 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2913 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2914 2 8224,
   opAt 2915 (.Dup ⟨2, by decide⟩),
   opAt 2916 .GT,
   pushAt 2917 2 3802,
   opAt 2918 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2951 .JUMPDEST,
   opAt 2952 (.Dup ⟨0, by decide⟩),
   opAt 2953 .MLOAD,
   opAt 2954 (.Dup ⟨1, by decide⟩),
   pushAt 2955 2 8256,
   opAt 2956 (.Swap ⟨0, by decide⟩),
   opAt 2957 .SUB,
   opAt 2958 .MLOAD,
   opAt 2959 (.Dup ⟨1, by decide⟩),
   opAt 2960 .ADD,
   opAt 2961 (.Dup ⟨0, by decide⟩),
   opAt 2962 (.Dup ⟨2, by decide⟩),
   opAt 2963 .GT,
   opAt 2964 (.Swap ⟨1, by decide⟩),
   opAt 2965 .POP,
   opAt 2966 (.Dup ⟨3, by decide⟩),
   opAt 2967 .ADD,
   opAt 2968 (.Dup ⟨0, by decide⟩),
   opAt 2969 (.Dup ⟨4, by decide⟩),
   opAt 2970 .GT,
   opAt 2971 (.Swap ⟨3, by decide⟩),
   opAt 2972 .POP,
   opAt 2973 (.Dup ⟨2, by decide⟩),
   opAt 2974 .MSTORE,
   opAt 2975 (.Swap ⟨0, by decide⟩),
   opAt 2976 (.Swap ⟨1, by decide⟩),
   opAt 2977 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2978 (.Swap ⟨0, by decide⟩),
   pushAt 2979 1 31,
   opAt 2980 .NOT,
   opAt 2981 .ADD,
   pushAt 2982 2 8255,
   opAt 2983 (.Dup ⟨1, by decide⟩),
   opAt 2984 .GT,
   pushAt 2985 2 3985,
   opAt 2986 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3008 .JUMPDEST,
   opAt 3009 (.Dup ⟨0, by decide⟩),
   opAt 3010 .MLOAD,
   pushAt 3011 2 8256,
   opAt 3012 (.Dup ⟨2, by decide⟩),
   opAt 3013 .SUB,
   opAt 3014 .MLOAD,
   opAt 3015 (.Dup ⟨1, by decide⟩),
   opAt 3016 (.Dup ⟨1, by decide⟩),
   opAt 3017 .GT,
   opAt 3018 (.Swap ⟨1, by decide⟩),
   opAt 3019 .SUB,
   opAt 3020 (.Dup ⟨3, by decide⟩),
   opAt 3021 (.Dup ⟨1, by decide⟩),
   opAt 3022 .LT,
   opAt 3023 (.Swap ⟨0, by decide⟩),
   opAt 3024 (.Dup ⟨4, by decide⟩),
   opAt 3025 (.Swap ⟨0, by decide⟩),
   opAt 3026 .SUB,
   opAt 3027 (.Dup ⟨3, by decide⟩),
   opAt 3028 .MSTORE,
   opAt 3029 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3030 (.Swap ⟨1, by decide⟩),
   opAt 3031 .POP,
   pushAt 3032 1 31,
   opAt 3033 .NOT,
   opAt 3034 .ADD,
   pushAt 3035 2 8255,
   opAt 3036 (.Dup ⟨1, by decide⟩),
   opAt 3037 .GT,
   pushAt 3038 2 4061,
   opAt 3039 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
