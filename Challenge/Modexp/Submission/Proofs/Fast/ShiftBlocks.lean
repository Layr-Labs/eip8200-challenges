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
  [opAt 2633 .JUMPDEST,
   opAt 2634 (.Dup ⟨0, by decide⟩),
   opAt 2635 .MLOAD,
   opAt 2636 .NOT,
   opAt 2637 (.Dup ⟨2, by decide⟩),
   opAt 2638 .ADD,
   opAt 2639 (.Dup ⟨2, by decide⟩),
   opAt 2640 (.Dup ⟨1, by decide⟩),
   opAt 2641 .LT,
   opAt 2642 (.Swap ⟨2, by decide⟩),
   opAt 2643 .POP,
   opAt 2644 (.Dup ⟨1, by decide⟩),
   pushAt 2645 2 1280,
   opAt 2646 .ADD,
   opAt 2647 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2648 (.Dup ⟨0, by decide⟩),
   opAt 2649 .ISZERO,
   pushAt 2650 2 3518,
   opAt 2651 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2840 .JUMPDEST,
   opAt 2841 (.Dup ⟨0, by decide⟩),
   opAt 2842 .MLOAD,
   pushAt 2843 0 0,
   opAt 2844 .NOT,
   opAt 2845 (.Dup ⟨6, by decide⟩),
   opAt 2846 (.Dup ⟨2, by decide⟩),
   opAt 2847 .MUL,
   opAt 2848 (.Swap ⟨1, by decide⟩),
   opAt 2849 (.Dup ⟨7, by decide⟩),
   opAt 2850 .MULMOD,
   opAt 2851 (.Dup ⟨1, by decide⟩),
   opAt 2852 (.Dup ⟨1, by decide⟩),
   opAt 2853 .LT,
   opAt 2854 .SUB,
   opAt 2855 (.Dup ⟨5, by decide⟩),
   opAt 2856 (.Dup ⟨2, by decide⟩),
   opAt 2857 .ADD,
   opAt 2858 (.Dup ⟨0, by decide⟩),
   opAt 2859 (.Swap ⟨6, by decide⟩),
   opAt 2860 .GT,
   opAt 2861 .SUB,
   opAt 2862 .SUB,
   opAt 2863 (.Dup ⟨4, by decide⟩),
   opAt 2864 (.Dup ⟨3, by decide⟩),
   opAt 2865 .MLOAD,
   opAt 2866 .ADD,
   opAt 2867 (.Dup ⟨0, by decide⟩),
   opAt 2868 (.Swap ⟨5, by decide⟩),
   opAt 2869 .GT,
   opAt 2870 .ADD,
   opAt 2871 (.Swap ⟨3, by decide⟩),
   opAt 2872 (.Dup ⟨2, by decide⟩),
   opAt 2873 (.Dup ⟨4, by decide⟩),
   opAt 2874 .ADD,
   opAt 2875 (.Swap ⟨2, by decide⟩),
   opAt 2876 .MSTORE,
   opAt 2877 (.Dup ⟨2, by decide⟩),
   opAt 2878 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2996 2 4128,
   opAt 2997 (.Dup ⟨2, by decide⟩),
   opAt 2998 .GT,
   pushAt 2999 2 3766,
   opAt 3000 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3034 .JUMPDEST,
   opAt 3035 (.Dup ⟨0, by decide⟩),
   opAt 3036 .MLOAD,
   opAt 3037 (.Dup ⟨1, by decide⟩),
   pushAt 3038 2 4160,
   opAt 3039 (.Swap ⟨0, by decide⟩),
   opAt 3040 .SUB,
   opAt 3041 .MLOAD,
   opAt 3042 (.Dup ⟨1, by decide⟩),
   opAt 3043 .ADD,
   opAt 3044 (.Dup ⟨0, by decide⟩),
   opAt 3045 (.Dup ⟨2, by decide⟩),
   opAt 3046 .GT,
   opAt 3047 (.Swap ⟨1, by decide⟩),
   opAt 3048 .POP,
   opAt 3049 (.Dup ⟨3, by decide⟩),
   opAt 3050 .ADD,
   opAt 3051 (.Dup ⟨0, by decide⟩),
   opAt 3052 (.Dup ⟨4, by decide⟩),
   opAt 3053 .GT,
   opAt 3054 (.Swap ⟨3, by decide⟩),
   opAt 3055 .POP,
   opAt 3056 (.Dup ⟨2, by decide⟩),
   opAt 3057 .MSTORE,
   opAt 3058 (.Swap ⟨0, by decide⟩),
   opAt 3059 (.Swap ⟨1, by decide⟩),
   opAt 3060 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3061 (.Swap ⟨0, by decide⟩),
   pushAt 3062 1 31,
   opAt 3063 .NOT,
   opAt 3064 .ADD,
   pushAt 3065 2 4159,
   opAt 3066 (.Dup ⟨1, by decide⟩),
   opAt 3067 .GT,
   pushAt 3068 2 3972,
   opAt 3069 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3091 .JUMPDEST,
   opAt 3092 (.Dup ⟨0, by decide⟩),
   opAt 3093 .MLOAD,
   pushAt 3094 2 4160,
   opAt 3095 (.Dup ⟨2, by decide⟩),
   opAt 3096 .SUB,
   opAt 3097 .MLOAD,
   opAt 3098 (.Dup ⟨1, by decide⟩),
   opAt 3099 (.Dup ⟨1, by decide⟩),
   opAt 3100 .GT,
   opAt 3101 (.Swap ⟨1, by decide⟩),
   opAt 3102 .SUB,
   opAt 3103 (.Dup ⟨3, by decide⟩),
   opAt 3104 (.Dup ⟨1, by decide⟩),
   opAt 3105 .LT,
   opAt 3106 (.Swap ⟨0, by decide⟩),
   opAt 3107 (.Dup ⟨4, by decide⟩),
   opAt 3108 (.Swap ⟨0, by decide⟩),
   opAt 3109 .SUB,
   opAt 3110 (.Dup ⟨3, by decide⟩),
   opAt 3111 .MSTORE,
   opAt 3112 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3113 (.Swap ⟨1, by decide⟩),
   opAt 3114 .POP,
   pushAt 3115 1 31,
   opAt 3116 .NOT,
   opAt 3117 .ADD,
   pushAt 3118 2 4159,
   opAt 3119 (.Dup ⟨1, by decide⟩),
   opAt 3120 .GT,
   pushAt 3121 2 4048,
   opAt 3122 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
