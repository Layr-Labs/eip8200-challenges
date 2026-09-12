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
  [opAt 2622 .JUMPDEST,
   opAt 2623 (.Dup ⟨0, by decide⟩),
   opAt 2624 .MLOAD,
   opAt 2625 .NOT,
   opAt 2626 (.Dup ⟨2, by decide⟩),
   opAt 2627 .ADD,
   opAt 2628 (.Dup ⟨2, by decide⟩),
   opAt 2629 (.Dup ⟨1, by decide⟩),
   opAt 2630 .LT,
   opAt 2631 (.Swap ⟨2, by decide⟩),
   opAt 2632 .POP,
   opAt 2633 (.Dup ⟨1, by decide⟩),
   pushAt 2634 2 1280,
   opAt 2635 .ADD,
   opAt 2636 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2637 (.Dup ⟨0, by decide⟩),
   opAt 2638 .ISZERO,
   pushAt 2639 2 3532,
   opAt 2640 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2829 .JUMPDEST,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   opAt 2831 .MLOAD,
   pushAt 2832 0 0,
   opAt 2833 .NOT,
   opAt 2834 (.Dup ⟨6, by decide⟩),
   opAt 2835 (.Dup ⟨2, by decide⟩),
   opAt 2836 .MUL,
   opAt 2837 (.Swap ⟨1, by decide⟩),
   opAt 2838 (.Dup ⟨7, by decide⟩),
   opAt 2839 .MULMOD,
   opAt 2840 (.Dup ⟨1, by decide⟩),
   opAt 2841 (.Dup ⟨1, by decide⟩),
   opAt 2842 .LT,
   opAt 2843 .SUB,
   opAt 2844 (.Dup ⟨5, by decide⟩),
   opAt 2845 (.Dup ⟨2, by decide⟩),
   opAt 2846 .ADD,
   opAt 2847 (.Dup ⟨0, by decide⟩),
   opAt 2848 (.Swap ⟨6, by decide⟩),
   opAt 2849 .GT,
   opAt 2850 .SUB,
   opAt 2851 .SUB,
   opAt 2852 (.Dup ⟨4, by decide⟩),
   opAt 2853 (.Dup ⟨3, by decide⟩),
   opAt 2854 .MLOAD,
   opAt 2855 .ADD,
   opAt 2856 (.Dup ⟨0, by decide⟩),
   opAt 2857 (.Swap ⟨5, by decide⟩),
   opAt 2858 .GT,
   opAt 2859 .ADD,
   opAt 2860 (.Swap ⟨3, by decide⟩),
   opAt 2861 (.Dup ⟨2, by decide⟩),
   opAt 2862 (.Dup ⟨4, by decide⟩),
   opAt 2863 .ADD,
   opAt 2864 (.Swap ⟨2, by decide⟩),
   opAt 2865 .MSTORE,
   opAt 2866 (.Dup ⟨2, by decide⟩),
   opAt 2867 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2985 2 4128,
   opAt 2986 (.Dup ⟨2, by decide⟩),
   opAt 2987 .GT,
   pushAt 2988 2 3780,
   opAt 2989 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3023 .JUMPDEST,
   opAt 3024 (.Dup ⟨0, by decide⟩),
   opAt 3025 .MLOAD,
   opAt 3026 (.Dup ⟨1, by decide⟩),
   pushAt 3027 2 4160,
   opAt 3028 (.Swap ⟨0, by decide⟩),
   opAt 3029 .SUB,
   opAt 3030 .MLOAD,
   opAt 3031 (.Dup ⟨1, by decide⟩),
   opAt 3032 .ADD,
   opAt 3033 (.Dup ⟨0, by decide⟩),
   opAt 3034 (.Dup ⟨2, by decide⟩),
   opAt 3035 .GT,
   opAt 3036 (.Swap ⟨1, by decide⟩),
   opAt 3037 .POP,
   opAt 3038 (.Dup ⟨3, by decide⟩),
   opAt 3039 .ADD,
   opAt 3040 (.Dup ⟨0, by decide⟩),
   opAt 3041 (.Dup ⟨4, by decide⟩),
   opAt 3042 .GT,
   opAt 3043 (.Swap ⟨3, by decide⟩),
   opAt 3044 .POP,
   opAt 3045 (.Dup ⟨2, by decide⟩),
   opAt 3046 .MSTORE,
   opAt 3047 (.Swap ⟨0, by decide⟩),
   opAt 3048 (.Swap ⟨1, by decide⟩),
   opAt 3049 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3050 (.Swap ⟨0, by decide⟩),
   pushAt 3051 1 31,
   opAt 3052 .NOT,
   opAt 3053 .ADD,
   pushAt 3054 2 4159,
   opAt 3055 (.Dup ⟨1, by decide⟩),
   opAt 3056 .GT,
   pushAt 3057 2 3986,
   opAt 3058 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3080 .JUMPDEST,
   opAt 3081 (.Dup ⟨0, by decide⟩),
   opAt 3082 .MLOAD,
   pushAt 3083 2 4160,
   opAt 3084 (.Dup ⟨2, by decide⟩),
   opAt 3085 .SUB,
   opAt 3086 .MLOAD,
   opAt 3087 (.Dup ⟨1, by decide⟩),
   opAt 3088 (.Dup ⟨1, by decide⟩),
   opAt 3089 .GT,
   opAt 3090 (.Swap ⟨1, by decide⟩),
   opAt 3091 .SUB,
   opAt 3092 (.Dup ⟨3, by decide⟩),
   opAt 3093 (.Dup ⟨1, by decide⟩),
   opAt 3094 .LT,
   opAt 3095 (.Swap ⟨0, by decide⟩),
   opAt 3096 (.Dup ⟨4, by decide⟩),
   opAt 3097 (.Swap ⟨0, by decide⟩),
   opAt 3098 .SUB,
   opAt 3099 (.Dup ⟨3, by decide⟩),
   opAt 3100 .MSTORE,
   opAt 3101 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3102 (.Swap ⟨1, by decide⟩),
   opAt 3103 .POP,
   pushAt 3104 1 31,
   opAt 3105 .NOT,
   opAt 3106 .ADD,
   pushAt 3107 2 4159,
   opAt 3108 (.Dup ⟨1, by decide⟩),
   opAt 3109 .GT,
   pushAt 3110 2 4062,
   opAt 3111 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
