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
  [opAt 2616 .JUMPDEST,
   opAt 2617 (.Dup ⟨0, by decide⟩),
   opAt 2618 .MLOAD,
   opAt 2619 .NOT,
   opAt 2620 (.Dup ⟨2, by decide⟩),
   opAt 2621 .ADD,
   opAt 2622 (.Dup ⟨2, by decide⟩),
   opAt 2623 (.Dup ⟨1, by decide⟩),
   opAt 2624 .LT,
   opAt 2625 (.Swap ⟨2, by decide⟩),
   opAt 2626 .POP,
   opAt 2627 (.Dup ⟨1, by decide⟩),
   pushAt 2628 2 1280,
   opAt 2629 .ADD,
   opAt 2630 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2631 (.Dup ⟨0, by decide⟩),
   opAt 2632 .ISZERO,
   pushAt 2633 2 3522,
   opAt 2634 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2823 .JUMPDEST,
   opAt 2824 (.Dup ⟨0, by decide⟩),
   opAt 2825 .MLOAD,
   pushAt 2826 0 0,
   opAt 2827 .NOT,
   opAt 2828 (.Dup ⟨6, by decide⟩),
   opAt 2829 (.Dup ⟨2, by decide⟩),
   opAt 2830 .MUL,
   opAt 2831 (.Swap ⟨1, by decide⟩),
   opAt 2832 (.Dup ⟨7, by decide⟩),
   opAt 2833 .MULMOD,
   opAt 2834 (.Dup ⟨1, by decide⟩),
   opAt 2835 (.Dup ⟨1, by decide⟩),
   opAt 2836 .LT,
   opAt 2837 .SUB,
   opAt 2838 (.Dup ⟨5, by decide⟩),
   opAt 2839 (.Dup ⟨2, by decide⟩),
   opAt 2840 .ADD,
   opAt 2841 (.Dup ⟨0, by decide⟩),
   opAt 2842 (.Swap ⟨6, by decide⟩),
   opAt 2843 .GT,
   opAt 2844 .SUB,
   opAt 2845 .SUB,
   opAt 2846 (.Dup ⟨4, by decide⟩),
   opAt 2847 (.Dup ⟨3, by decide⟩),
   opAt 2848 .MLOAD,
   opAt 2849 .ADD,
   opAt 2850 (.Dup ⟨0, by decide⟩),
   opAt 2851 (.Swap ⟨5, by decide⟩),
   opAt 2852 .GT,
   opAt 2853 .ADD,
   opAt 2854 (.Swap ⟨3, by decide⟩),
   opAt 2855 (.Dup ⟨2, by decide⟩),
   opAt 2856 (.Dup ⟨4, by decide⟩),
   opAt 2857 .ADD,
   opAt 2858 (.Swap ⟨2, by decide⟩),
   opAt 2859 .MSTORE,
   opAt 2860 (.Dup ⟨2, by decide⟩),
   opAt 2861 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2979 2 2080,
   opAt 2980 (.Dup ⟨2, by decide⟩),
   opAt 2981 .GT,
   pushAt 2982 2 3770,
   opAt 2983 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3017 .JUMPDEST,
   opAt 3018 (.Dup ⟨0, by decide⟩),
   opAt 3019 .MLOAD,
   opAt 3020 (.Dup ⟨1, by decide⟩),
   pushAt 3021 2 2112,
   opAt 3022 (.Swap ⟨0, by decide⟩),
   opAt 3023 .SUB,
   opAt 3024 .MLOAD,
   opAt 3025 (.Dup ⟨1, by decide⟩),
   opAt 3026 .ADD,
   opAt 3027 (.Dup ⟨0, by decide⟩),
   opAt 3028 (.Dup ⟨2, by decide⟩),
   opAt 3029 .GT,
   opAt 3030 (.Swap ⟨1, by decide⟩),
   opAt 3031 .POP,
   opAt 3032 (.Dup ⟨3, by decide⟩),
   opAt 3033 .ADD,
   opAt 3034 (.Dup ⟨0, by decide⟩),
   opAt 3035 (.Dup ⟨4, by decide⟩),
   opAt 3036 .GT,
   opAt 3037 (.Swap ⟨3, by decide⟩),
   opAt 3038 .POP,
   opAt 3039 (.Dup ⟨2, by decide⟩),
   opAt 3040 .MSTORE,
   opAt 3041 (.Swap ⟨0, by decide⟩),
   opAt 3042 (.Swap ⟨1, by decide⟩),
   opAt 3043 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3044 (.Swap ⟨0, by decide⟩),
   pushAt 3045 1 31,
   opAt 3046 .NOT,
   opAt 3047 .ADD,
   pushAt 3048 2 2111,
   opAt 3049 (.Dup ⟨1, by decide⟩),
   opAt 3050 .GT,
   pushAt 3051 2 3976,
   opAt 3052 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3074 .JUMPDEST,
   opAt 3075 (.Dup ⟨0, by decide⟩),
   opAt 3076 .MLOAD,
   pushAt 3077 2 2112,
   opAt 3078 (.Dup ⟨2, by decide⟩),
   opAt 3079 .SUB,
   opAt 3080 .MLOAD,
   opAt 3081 (.Dup ⟨1, by decide⟩),
   opAt 3082 (.Dup ⟨1, by decide⟩),
   opAt 3083 .GT,
   opAt 3084 (.Swap ⟨1, by decide⟩),
   opAt 3085 .SUB,
   opAt 3086 (.Dup ⟨3, by decide⟩),
   opAt 3087 (.Dup ⟨1, by decide⟩),
   opAt 3088 .LT,
   opAt 3089 (.Swap ⟨0, by decide⟩),
   opAt 3090 (.Dup ⟨4, by decide⟩),
   opAt 3091 (.Swap ⟨0, by decide⟩),
   opAt 3092 .SUB,
   opAt 3093 (.Dup ⟨3, by decide⟩),
   opAt 3094 .MSTORE,
   opAt 3095 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3096 (.Swap ⟨1, by decide⟩),
   opAt 3097 .POP,
   pushAt 3098 1 31,
   opAt 3099 .NOT,
   opAt 3100 .ADD,
   pushAt 3101 2 2111,
   opAt 3102 (.Dup ⟨1, by decide⟩),
   opAt 3103 .GT,
   pushAt 3104 2 4052,
   opAt 3105 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
