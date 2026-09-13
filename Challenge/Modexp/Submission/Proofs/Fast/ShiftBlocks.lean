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
  [opAt 2567 .JUMPDEST,
   opAt 2568 (.Dup ⟨0, by decide⟩),
   opAt 2569 .MLOAD,
   opAt 2570 .NOT,
   opAt 2571 (.Dup ⟨2, by decide⟩),
   opAt 2572 .ADD,
   opAt 2573 (.Dup ⟨2, by decide⟩),
   opAt 2574 (.Dup ⟨1, by decide⟩),
   opAt 2575 .LT,
   opAt 2576 (.Swap ⟨2, by decide⟩),
   opAt 2577 .POP,
   opAt 2578 (.Dup ⟨1, by decide⟩),
   pushAt 2579 2 1280,
   opAt 2580 .ADD,
   opAt 2581 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 (.Dup ⟨0, by decide⟩),
   opAt 2583 .ISZERO,
   pushAt 2584 2 3473,
   opAt 2585 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2769 .JUMPDEST,
   pushAt 2770 2 832,
   opAt 2771 (.Dup ⟨1, by decide⟩),
   opAt 2772 .SUB,
   opAt 2773 .MLOAD,
   opAt 2774 (.Dup ⟨2, by decide⟩),
   opAt 2775 (.Dup ⟨6, by decide⟩),
   opAt 2776 (.Dup ⟨2, by decide⟩),
   opAt 2777 .MUL,
   opAt 2778 (.Swap ⟨1, by decide⟩),
   opAt 2779 (.Dup ⟨7, by decide⟩),
   opAt 2780 .MULMOD,
   opAt 2781 (.Dup ⟨1, by decide⟩),
   opAt 2782 (.Dup ⟨1, by decide⟩),
   opAt 2783 .LT,
   opAt 2784 .SUB,
   opAt 2785 (.Dup ⟨5, by decide⟩),
   opAt 2786 (.Dup ⟨2, by decide⟩),
   opAt 2787 .ADD,
   opAt 2788 (.Dup ⟨0, by decide⟩),
   opAt 2789 (.Swap ⟨6, by decide⟩),
   opAt 2790 .GT,
   opAt 2791 .SUB,
   opAt 2792 .SUB,
   opAt 2793 (.Dup ⟨4, by decide⟩),
   opAt 2794 (.Dup ⟨2, by decide⟩),
   opAt 2795 .MLOAD,
   opAt 2796 .ADD,
   opAt 2797 (.Dup ⟨0, by decide⟩),
   opAt 2798 (.Swap ⟨5, by decide⟩),
   opAt 2799 .GT,
   opAt 2800 .ADD,
   opAt 2801 (.Swap ⟨3, by decide⟩),
   opAt 2802 (.Dup ⟨1, by decide⟩),
   opAt 2803 .MSTORE,
   opAt 2804 (.Dup ⟨2, by decide⟩),
   opAt 2805 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2917 2 2080,
   opAt 2918 (.Dup ⟨1, by decide⟩),
   opAt 2919 .GT,
   pushAt 2920 2 3721,
   opAt 2921 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2955 .JUMPDEST,
   opAt 2956 (.Dup ⟨0, by decide⟩),
   opAt 2957 .MLOAD,
   opAt 2958 (.Dup ⟨1, by decide⟩),
   pushAt 2959 2 2112,
   opAt 2960 (.Swap ⟨0, by decide⟩),
   opAt 2961 .SUB,
   opAt 2962 .MLOAD,
   opAt 2963 (.Dup ⟨1, by decide⟩),
   opAt 2964 .ADD,
   opAt 2965 (.Dup ⟨0, by decide⟩),
   opAt 2966 (.Dup ⟨2, by decide⟩),
   opAt 2967 .GT,
   opAt 2968 (.Swap ⟨1, by decide⟩),
   opAt 2969 .POP,
   opAt 2970 (.Dup ⟨3, by decide⟩),
   opAt 2971 .ADD,
   opAt 2972 (.Dup ⟨0, by decide⟩),
   opAt 2973 (.Dup ⟨4, by decide⟩),
   opAt 2974 .GT,
   opAt 2975 (.Swap ⟨3, by decide⟩),
   opAt 2976 .POP,
   opAt 2977 (.Dup ⟨2, by decide⟩),
   opAt 2978 .MSTORE,
   opAt 2979 (.Swap ⟨0, by decide⟩),
   opAt 2980 (.Swap ⟨1, by decide⟩),
   opAt 2981 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2982 (.Swap ⟨0, by decide⟩),
   pushAt 2983 1 31,
   opAt 2984 .NOT,
   opAt 2985 .ADD,
   pushAt 2986 2 2111,
   opAt 2987 (.Dup ⟨1, by decide⟩),
   opAt 2988 .GT,
   pushAt 2989 2 3927,
   opAt 2990 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3012 .JUMPDEST,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 .MLOAD,
   pushAt 3015 2 2112,
   opAt 3016 (.Dup ⟨2, by decide⟩),
   opAt 3017 .SUB,
   opAt 3018 .MLOAD,
   opAt 3019 (.Dup ⟨1, by decide⟩),
   opAt 3020 (.Dup ⟨1, by decide⟩),
   opAt 3021 .GT,
   opAt 3022 (.Swap ⟨1, by decide⟩),
   opAt 3023 .SUB,
   opAt 3024 (.Dup ⟨3, by decide⟩),
   opAt 3025 (.Dup ⟨1, by decide⟩),
   opAt 3026 .LT,
   opAt 3027 (.Swap ⟨0, by decide⟩),
   opAt 3028 (.Dup ⟨4, by decide⟩),
   opAt 3029 (.Swap ⟨0, by decide⟩),
   opAt 3030 .SUB,
   opAt 3031 (.Dup ⟨3, by decide⟩),
   opAt 3032 .MSTORE,
   opAt 3033 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3034 (.Swap ⟨1, by decide⟩),
   opAt 3035 .POP,
   pushAt 3036 1 31,
   opAt 3037 .NOT,
   opAt 3038 .ADD,
   pushAt 3039 2 2111,
   opAt 3040 (.Dup ⟨1, by decide⟩),
   opAt 3041 .GT,
   pushAt 3042 2 4003,
   opAt 3043 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
