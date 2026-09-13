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

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2589 (.Dup ⟨0, by decide⟩),
   pushAt 2590 1 31,
   opAt 2591 .NOT,
   opAt 2592 .ADD,
   opAt 2593 (.Swap ⟨0, by decide⟩),
   pushAt 2594 2 3442,
   opAt 2595 .JUMPI]

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
   pushAt 2938 2 3717,
   opAt 2939 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2979 .JUMPDEST,
   opAt 2980 (.Dup ⟨0, by decide⟩),
   opAt 2981 .MLOAD,
   opAt 2982 (.Dup ⟨1, by decide⟩),
   pushAt 2983 2 2112,
   opAt 2984 (.Swap ⟨0, by decide⟩),
   opAt 2985 .SUB,
   opAt 2986 .MLOAD,
   opAt 2987 (.Dup ⟨1, by decide⟩),
   opAt 2988 .ADD,
   opAt 2989 (.Dup ⟨0, by decide⟩),
   opAt 2990 (.Dup ⟨2, by decide⟩),
   opAt 2991 .GT,
   opAt 2992 (.Swap ⟨1, by decide⟩),
   opAt 2993 .POP,
   opAt 2994 (.Dup ⟨3, by decide⟩),
   opAt 2995 .ADD,
   opAt 2996 (.Dup ⟨0, by decide⟩),
   opAt 2997 (.Dup ⟨4, by decide⟩),
   opAt 2998 .GT,
   opAt 2999 (.Swap ⟨3, by decide⟩),
   opAt 3000 .POP,
   opAt 3001 (.Dup ⟨2, by decide⟩),
   opAt 3002 .MSTORE,
   opAt 3003 (.Swap ⟨0, by decide⟩),
   opAt 3004 (.Swap ⟨1, by decide⟩),
   opAt 3005 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3006 (.Swap ⟨0, by decide⟩),
   pushAt 3007 1 31,
   opAt 3008 .NOT,
   opAt 3009 .ADD,
   pushAt 3010 2 2111,
   opAt 3011 (.Dup ⟨1, by decide⟩),
   opAt 3012 .GT,
   pushAt 3013 2 3937,
   opAt 3014 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3039 .JUMPDEST,
   opAt 3040 (.Dup ⟨0, by decide⟩),
   opAt 3041 .MLOAD,
   pushAt 3042 2 2112,
   opAt 3043 (.Dup ⟨2, by decide⟩),
   opAt 3044 .SUB,
   opAt 3045 .MLOAD,
   opAt 3046 (.Dup ⟨1, by decide⟩),
   opAt 3047 (.Dup ⟨1, by decide⟩),
   opAt 3048 .GT,
   opAt 3049 (.Swap ⟨1, by decide⟩),
   opAt 3050 .SUB,
   opAt 3051 (.Dup ⟨3, by decide⟩),
   opAt 3052 (.Dup ⟨1, by decide⟩),
   opAt 3053 .LT,
   opAt 3054 (.Swap ⟨0, by decide⟩),
   opAt 3055 (.Dup ⟨4, by decide⟩),
   opAt 3056 (.Swap ⟨0, by decide⟩),
   opAt 3057 .SUB,
   opAt 3058 (.Dup ⟨3, by decide⟩),
   opAt 3059 .MSTORE,
   opAt 3060 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3061 (.Swap ⟨1, by decide⟩),
   opAt 3062 .POP,
   pushAt 3063 1 31,
   opAt 3064 .NOT,
   opAt 3065 .ADD,
   pushAt 3066 2 2111,
   opAt 3067 (.Dup ⟨1, by decide⟩),
   opAt 3068 .GT,
   pushAt 3069 2 4016,
   opAt 3070 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
