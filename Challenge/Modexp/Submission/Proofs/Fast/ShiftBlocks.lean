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
  [opAt 2572 .JUMPDEST,
   opAt 2573 (.Dup ⟨0, by decide⟩),
   opAt 2574 .MLOAD,
   opAt 2575 .NOT,
   opAt 2576 (.Dup ⟨2, by decide⟩),
   opAt 2577 .ADD,
   opAt 2578 (.Dup ⟨2, by decide⟩),
   opAt 2579 (.Dup ⟨1, by decide⟩),
   opAt 2580 .LT,
   opAt 2581 (.Swap ⟨2, by decide⟩),
   opAt 2582 .POP,
   opAt 2583 (.Dup ⟨1, by decide⟩),
   pushAt 2584 2 1280,
   opAt 2585 .ADD,
   opAt 2586 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2587 (.Dup ⟨0, by decide⟩),
   opAt 2588 .ISZERO,
   pushAt 2589 2 3473,
   opAt 2590 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2779 .JUMPDEST,
   opAt 2780 (.Dup ⟨0, by decide⟩),
   opAt 2781 .MLOAD,
   pushAt 2782 0 0,
   opAt 2783 .NOT,
   opAt 2784 (.Dup ⟨6, by decide⟩),
   opAt 2785 (.Dup ⟨2, by decide⟩),
   opAt 2786 .MUL,
   opAt 2787 (.Swap ⟨1, by decide⟩),
   opAt 2788 (.Dup ⟨7, by decide⟩),
   opAt 2789 .MULMOD,
   opAt 2790 (.Dup ⟨1, by decide⟩),
   opAt 2791 (.Dup ⟨1, by decide⟩),
   opAt 2792 .LT,
   opAt 2793 .SUB,
   opAt 2794 (.Dup ⟨5, by decide⟩),
   opAt 2795 (.Dup ⟨2, by decide⟩),
   opAt 2796 .ADD,
   opAt 2797 (.Dup ⟨0, by decide⟩),
   opAt 2798 (.Swap ⟨6, by decide⟩),
   opAt 2799 .GT,
   opAt 2800 .SUB,
   opAt 2801 .SUB,
   opAt 2802 (.Dup ⟨4, by decide⟩),
   opAt 2803 (.Dup ⟨3, by decide⟩),
   opAt 2804 .MLOAD,
   opAt 2805 .ADD,
   opAt 2806 (.Dup ⟨0, by decide⟩),
   opAt 2807 (.Swap ⟨5, by decide⟩),
   opAt 2808 .GT,
   opAt 2809 .ADD,
   opAt 2810 (.Swap ⟨3, by decide⟩),
   opAt 2811 (.Dup ⟨2, by decide⟩),
   opAt 2812 (.Dup ⟨4, by decide⟩),
   opAt 2813 .ADD,
   opAt 2814 (.Swap ⟨2, by decide⟩),
   opAt 2815 .MSTORE,
   opAt 2816 (.Dup ⟨2, by decide⟩),
   opAt 2817 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2935 2 2080,
   opAt 2936 (.Dup ⟨2, by decide⟩),
   opAt 2937 .GT,
   pushAt 2938 2 3721,
   opAt 2939 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2973 .JUMPDEST,
   opAt 2974 (.Dup ⟨0, by decide⟩),
   opAt 2975 .MLOAD,
   opAt 2976 (.Dup ⟨1, by decide⟩),
   pushAt 2977 2 2112,
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
   pushAt 3001 1 31,
   opAt 3002 .NOT,
   opAt 3003 .ADD,
   pushAt 3004 2 2111,
   opAt 3005 (.Dup ⟨1, by decide⟩),
   opAt 3006 .GT,
   pushAt 3007 2 3927,
   opAt 3008 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3030 .JUMPDEST,
   opAt 3031 (.Dup ⟨0, by decide⟩),
   opAt 3032 .MLOAD,
   pushAt 3033 2 2112,
   opAt 3034 (.Dup ⟨2, by decide⟩),
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
   pushAt 3054 1 31,
   opAt 3055 .NOT,
   opAt 3056 .ADD,
   pushAt 3057 2 2111,
   opAt 3058 (.Dup ⟨1, by decide⟩),
   opAt 3059 .GT,
   pushAt 3060 2 4003,
   opAt 3061 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
