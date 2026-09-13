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
  [opAt 2574 .JUMPDEST,
   opAt 2575 (.Dup ⟨0, by decide⟩),
   opAt 2576 .MLOAD,
   opAt 2577 .NOT,
   opAt 2578 (.Dup ⟨2, by decide⟩),
   opAt 2579 .ADD,
   opAt 2580 (.Dup ⟨2, by decide⟩),
   opAt 2581 (.Dup ⟨1, by decide⟩),
   opAt 2582 .LT,
   opAt 2583 (.Swap ⟨2, by decide⟩),
   opAt 2584 .POP,
   opAt 2585 (.Dup ⟨1, by decide⟩),
   pushAt 2586 2 1280,
   opAt 2587 .ADD,
   opAt 2588 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2589 (.Dup ⟨0, by decide⟩),
   opAt 2590 .ISZERO,
   pushAt 2591 2 3473,
   opAt 2592 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2781 .JUMPDEST,
   opAt 2782 (.Dup ⟨0, by decide⟩),
   opAt 2783 .MLOAD,
   pushAt 2784 0 0,
   opAt 2785 .NOT,
   opAt 2786 (.Dup ⟨6, by decide⟩),
   opAt 2787 (.Dup ⟨2, by decide⟩),
   opAt 2788 .MUL,
   opAt 2789 (.Swap ⟨1, by decide⟩),
   opAt 2790 (.Dup ⟨7, by decide⟩),
   opAt 2791 .MULMOD,
   opAt 2792 (.Dup ⟨1, by decide⟩),
   opAt 2793 (.Dup ⟨1, by decide⟩),
   opAt 2794 .LT,
   opAt 2795 .SUB,
   opAt 2796 (.Dup ⟨5, by decide⟩),
   opAt 2797 (.Dup ⟨2, by decide⟩),
   opAt 2798 .ADD,
   opAt 2799 (.Dup ⟨0, by decide⟩),
   opAt 2800 (.Swap ⟨6, by decide⟩),
   opAt 2801 .GT,
   opAt 2802 .SUB,
   opAt 2803 .SUB,
   opAt 2804 (.Dup ⟨4, by decide⟩),
   opAt 2805 (.Dup ⟨3, by decide⟩),
   opAt 2806 .MLOAD,
   opAt 2807 .ADD,
   opAt 2808 (.Dup ⟨0, by decide⟩),
   opAt 2809 (.Swap ⟨5, by decide⟩),
   opAt 2810 .GT,
   opAt 2811 .ADD,
   opAt 2812 (.Swap ⟨3, by decide⟩),
   opAt 2813 (.Dup ⟨2, by decide⟩),
   opAt 2814 (.Dup ⟨4, by decide⟩),
   opAt 2815 .ADD,
   opAt 2816 (.Swap ⟨2, by decide⟩),
   opAt 2817 .MSTORE,
   opAt 2818 (.Dup ⟨2, by decide⟩),
   opAt 2819 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2937 2 2080,
   opAt 2938 (.Dup ⟨2, by decide⟩),
   opAt 2939 .GT,
   pushAt 2940 2 3721,
   opAt 2941 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2975 .JUMPDEST,
   opAt 2976 (.Dup ⟨0, by decide⟩),
   opAt 2977 .MLOAD,
   opAt 2978 (.Dup ⟨1, by decide⟩),
   pushAt 2979 2 2112,
   opAt 2980 (.Swap ⟨0, by decide⟩),
   opAt 2981 .SUB,
   opAt 2982 .MLOAD,
   opAt 2983 (.Dup ⟨1, by decide⟩),
   opAt 2984 .ADD,
   opAt 2985 (.Dup ⟨0, by decide⟩),
   opAt 2986 (.Dup ⟨2, by decide⟩),
   opAt 2987 .GT,
   opAt 2988 (.Swap ⟨1, by decide⟩),
   opAt 2989 .POP,
   opAt 2990 (.Dup ⟨3, by decide⟩),
   opAt 2991 .ADD,
   opAt 2992 (.Dup ⟨0, by decide⟩),
   opAt 2993 (.Dup ⟨4, by decide⟩),
   opAt 2994 .GT,
   opAt 2995 (.Swap ⟨3, by decide⟩),
   opAt 2996 .POP,
   opAt 2997 (.Dup ⟨2, by decide⟩),
   opAt 2998 .MSTORE,
   opAt 2999 (.Swap ⟨0, by decide⟩),
   opAt 3000 (.Swap ⟨1, by decide⟩),
   opAt 3001 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3002 (.Swap ⟨0, by decide⟩),
   pushAt 3003 1 31,
   opAt 3004 .NOT,
   opAt 3005 .ADD,
   pushAt 3006 2 2111,
   opAt 3007 (.Dup ⟨1, by decide⟩),
   opAt 3008 .GT,
   pushAt 3009 2 3927,
   opAt 3010 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3032 .JUMPDEST,
   opAt 3033 (.Dup ⟨0, by decide⟩),
   opAt 3034 .MLOAD,
   pushAt 3035 2 2112,
   opAt 3036 (.Dup ⟨2, by decide⟩),
   opAt 3037 .SUB,
   opAt 3038 .MLOAD,
   opAt 3039 (.Dup ⟨1, by decide⟩),
   opAt 3040 (.Dup ⟨1, by decide⟩),
   opAt 3041 .GT,
   opAt 3042 (.Swap ⟨1, by decide⟩),
   opAt 3043 .SUB,
   opAt 3044 (.Dup ⟨3, by decide⟩),
   opAt 3045 (.Dup ⟨1, by decide⟩),
   opAt 3046 .LT,
   opAt 3047 (.Swap ⟨0, by decide⟩),
   opAt 3048 (.Dup ⟨4, by decide⟩),
   opAt 3049 (.Swap ⟨0, by decide⟩),
   opAt 3050 .SUB,
   opAt 3051 (.Dup ⟨3, by decide⟩),
   opAt 3052 .MSTORE,
   opAt 3053 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3054 (.Swap ⟨1, by decide⟩),
   opAt 3055 .POP,
   pushAt 3056 1 31,
   opAt 3057 .NOT,
   opAt 3058 .ADD,
   pushAt 3059 2 2111,
   opAt 3060 (.Dup ⟨1, by decide⟩),
   opAt 3061 .GT,
   pushAt 3062 2 4003,
   opAt 3063 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
