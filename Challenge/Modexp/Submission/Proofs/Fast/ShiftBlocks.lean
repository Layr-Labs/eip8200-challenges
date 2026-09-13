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
  [opAt 2568 .JUMPDEST,
   opAt 2569 (.Dup ⟨0, by decide⟩),
   opAt 2570 .MLOAD,
   opAt 2571 .NOT,
   opAt 2572 (.Dup ⟨2, by decide⟩),
   opAt 2573 .ADD,
   opAt 2574 (.Dup ⟨2, by decide⟩),
   opAt 2575 (.Dup ⟨1, by decide⟩),
   opAt 2576 .LT,
   opAt 2577 (.Swap ⟨2, by decide⟩),
   opAt 2578 .POP,
   opAt 2579 (.Dup ⟨1, by decide⟩),
   pushAt 2580 2 1280,
   opAt 2581 .ADD,
   opAt 2582 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2583 (.Dup ⟨0, by decide⟩),
   opAt 2584 .ISZERO,
   pushAt 2585 2 3473,
   opAt 2586 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2770 .JUMPDEST,
   pushAt 2771 2 832,
   opAt 2772 (.Dup ⟨1, by decide⟩),
   opAt 2773 .SUB,
   opAt 2774 .MLOAD,
   opAt 2775 (.Dup ⟨2, by decide⟩),
   opAt 2776 (.Dup ⟨6, by decide⟩),
   opAt 2777 (.Dup ⟨2, by decide⟩),
   opAt 2778 .MUL,
   opAt 2779 (.Swap ⟨1, by decide⟩),
   opAt 2780 (.Dup ⟨7, by decide⟩),
   opAt 2781 .MULMOD,
   opAt 2782 (.Dup ⟨1, by decide⟩),
   opAt 2783 (.Dup ⟨1, by decide⟩),
   opAt 2784 .LT,
   opAt 2785 .SUB,
   opAt 2786 (.Dup ⟨5, by decide⟩),
   opAt 2787 (.Dup ⟨2, by decide⟩),
   opAt 2788 .ADD,
   opAt 2789 (.Dup ⟨0, by decide⟩),
   opAt 2790 (.Swap ⟨6, by decide⟩),
   opAt 2791 .GT,
   opAt 2792 .SUB,
   opAt 2793 .SUB,
   opAt 2794 (.Dup ⟨4, by decide⟩),
   opAt 2795 (.Dup ⟨2, by decide⟩),
   opAt 2796 .MLOAD,
   opAt 2797 .ADD,
   opAt 2798 (.Dup ⟨0, by decide⟩),
   opAt 2799 (.Swap ⟨5, by decide⟩),
   opAt 2800 .GT,
   opAt 2801 .ADD,
   opAt 2802 (.Swap ⟨3, by decide⟩),
   opAt 2803 (.Dup ⟨1, by decide⟩),
   opAt 2804 .MSTORE,
   opAt 2805 (.Dup ⟨2, by decide⟩),
   opAt 2806 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2918 2 2080,
   opAt 2919 (.Dup ⟨1, by decide⟩),
   opAt 2920 .GT,
   pushAt 2921 2 3721,
   opAt 2922 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2956 .JUMPDEST,
   opAt 2957 (.Dup ⟨0, by decide⟩),
   opAt 2958 .MLOAD,
   opAt 2959 (.Dup ⟨1, by decide⟩),
   pushAt 2960 2 2112,
   opAt 2961 (.Swap ⟨0, by decide⟩),
   opAt 2962 .SUB,
   opAt 2963 .MLOAD,
   opAt 2964 (.Dup ⟨1, by decide⟩),
   opAt 2965 .ADD,
   opAt 2966 (.Dup ⟨0, by decide⟩),
   opAt 2967 (.Dup ⟨2, by decide⟩),
   opAt 2968 .GT,
   opAt 2969 (.Swap ⟨1, by decide⟩),
   opAt 2970 .POP,
   opAt 2971 (.Dup ⟨3, by decide⟩),
   opAt 2972 .ADD,
   opAt 2973 (.Dup ⟨0, by decide⟩),
   opAt 2974 (.Dup ⟨4, by decide⟩),
   opAt 2975 .GT,
   opAt 2976 (.Swap ⟨3, by decide⟩),
   opAt 2977 .POP,
   opAt 2978 (.Dup ⟨2, by decide⟩),
   opAt 2979 .MSTORE,
   opAt 2980 (.Swap ⟨0, by decide⟩),
   opAt 2981 (.Swap ⟨1, by decide⟩),
   opAt 2982 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2983 (.Swap ⟨0, by decide⟩),
   pushAt 2984 1 31,
   opAt 2985 .NOT,
   opAt 2986 .ADD,
   pushAt 2987 2 2111,
   opAt 2988 (.Dup ⟨1, by decide⟩),
   opAt 2989 .GT,
   pushAt 2990 2 3927,
   opAt 2991 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3013 .JUMPDEST,
   opAt 3014 (.Dup ⟨0, by decide⟩),
   opAt 3015 .MLOAD,
   pushAt 3016 2 2112,
   opAt 3017 (.Dup ⟨2, by decide⟩),
   opAt 3018 .SUB,
   opAt 3019 .MLOAD,
   opAt 3020 (.Dup ⟨1, by decide⟩),
   opAt 3021 (.Dup ⟨1, by decide⟩),
   opAt 3022 .GT,
   opAt 3023 (.Swap ⟨1, by decide⟩),
   opAt 3024 .SUB,
   opAt 3025 (.Dup ⟨3, by decide⟩),
   opAt 3026 (.Dup ⟨1, by decide⟩),
   opAt 3027 .LT,
   opAt 3028 (.Swap ⟨0, by decide⟩),
   opAt 3029 (.Dup ⟨4, by decide⟩),
   opAt 3030 (.Swap ⟨0, by decide⟩),
   opAt 3031 .SUB,
   opAt 3032 (.Dup ⟨3, by decide⟩),
   opAt 3033 .MSTORE,
   opAt 3034 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3035 (.Swap ⟨1, by decide⟩),
   opAt 3036 .POP,
   pushAt 3037 1 31,
   opAt 3038 .NOT,
   opAt 3039 .ADD,
   pushAt 3040 2 2111,
   opAt 3041 (.Dup ⟨1, by decide⟩),
   opAt 3042 .GT,
   pushAt 3043 2 4003,
   opAt 3044 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
