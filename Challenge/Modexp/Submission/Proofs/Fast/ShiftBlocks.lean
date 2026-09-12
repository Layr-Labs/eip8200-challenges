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
  [opAt 2619 .JUMPDEST,
   opAt 2620 (.Dup ⟨0, by decide⟩),
   opAt 2621 .MLOAD,
   opAt 2622 .NOT,
   opAt 2623 (.Dup ⟨2, by decide⟩),
   opAt 2624 .ADD,
   opAt 2625 (.Dup ⟨2, by decide⟩),
   opAt 2626 (.Dup ⟨1, by decide⟩),
   opAt 2627 .LT,
   opAt 2628 (.Swap ⟨2, by decide⟩),
   opAt 2629 .POP,
   opAt 2630 (.Dup ⟨1, by decide⟩),
   pushAt 2631 2 1280,
   opAt 2632 .ADD,
   opAt 2633 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2634 (.Dup ⟨0, by decide⟩),
   opAt 2635 .ISZERO,
   pushAt 2636 2 3536,
   opAt 2637 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..38). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2812 .JUMPDEST,
   opAt 2813 (.Dup ⟨0, by decide⟩),
   opAt 2814 .MLOAD,
   pushAt 2815 0 0,
   opAt 2816 .NOT,
   opAt 2817 (.Dup ⟨6, by decide⟩),
   opAt 2818 (.Dup ⟨2, by decide⟩),
   opAt 2819 .MUL,
   opAt 2820 (.Swap ⟨1, by decide⟩),
   opAt 2821 (.Dup ⟨7, by decide⟩),
   opAt 2822 .MULMOD,
   opAt 2823 (.Dup ⟨1, by decide⟩),
   opAt 2824 (.Dup ⟨1, by decide⟩),
   opAt 2825 .LT,
   opAt 2826 .SUB,
   opAt 2827 (.Dup ⟨5, by decide⟩),
   opAt 2828 (.Dup ⟨2, by decide⟩),
   opAt 2829 .ADD,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   opAt 2831 (.Swap ⟨6, by decide⟩),
   opAt 2832 .GT,
   opAt 2833 .SUB,
   opAt 2834 .SUB,
   opAt 2835 (.Dup ⟨4, by decide⟩),
   opAt 2836 (.Dup ⟨3, by decide⟩),
   opAt 2837 .MLOAD,
   opAt 2838 .ADD,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   opAt 2840 (.Swap ⟨5, by decide⟩),
   opAt 2841 .GT,
   opAt 2842 .ADD,
   opAt 2843 (.Swap ⟨3, by decide⟩),
   opAt 2844 (.Dup ⟨2, by decide⟩),
   opAt 2845 (.Dup ⟨4, by decide⟩),
   opAt 2846 .ADD,
   opAt 2847 (.Swap ⟨2, by decide⟩),
   opAt 2848 .MSTORE,
   opAt 2849 (.Dup ⟨2, by decide⟩),
   opAt 2850 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 39..43). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2851 32 4128,
   opAt 2852 (.Dup ⟨2, by decide⟩),
   opAt 2853 .GT,
   pushAt 2854 2 3762,
   opAt 2855 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2889 .JUMPDEST,
   opAt 2890 (.Dup ⟨0, by decide⟩),
   opAt 2891 .MLOAD,
   opAt 2892 (.Dup ⟨1, by decide⟩),
   pushAt 2893 2 4160,
   opAt 2894 (.Swap ⟨0, by decide⟩),
   opAt 2895 .SUB,
   opAt 2896 .MLOAD,
   opAt 2897 (.Dup ⟨1, by decide⟩),
   opAt 2898 .ADD,
   opAt 2899 (.Dup ⟨0, by decide⟩),
   opAt 2900 (.Dup ⟨2, by decide⟩),
   opAt 2901 .GT,
   opAt 2902 (.Swap ⟨1, by decide⟩),
   opAt 2903 .POP,
   opAt 2904 (.Dup ⟨3, by decide⟩),
   opAt 2905 .ADD,
   opAt 2906 (.Dup ⟨0, by decide⟩),
   opAt 2907 (.Dup ⟨4, by decide⟩),
   opAt 2908 .GT,
   opAt 2909 (.Swap ⟨3, by decide⟩),
   opAt 2910 .POP,
   opAt 2911 (.Dup ⟨2, by decide⟩),
   opAt 2912 .MSTORE,
   opAt 2913 (.Swap ⟨0, by decide⟩),
   opAt 2914 (.Swap ⟨1, by decide⟩),
   opAt 2915 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2916 (.Swap ⟨0, by decide⟩),
   pushAt 2917 1 31,
   opAt 2918 .NOT,
   opAt 2919 .ADD,
   pushAt 2920 2 4159,
   opAt 2921 (.Dup ⟨1, by decide⟩),
   opAt 2922 .GT,
   pushAt 2923 2 3881,
   opAt 2924 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2946 .JUMPDEST,
   opAt 2947 (.Dup ⟨0, by decide⟩),
   opAt 2948 .MLOAD,
   pushAt 2949 2 4160,
   opAt 2950 (.Dup ⟨2, by decide⟩),
   opAt 2951 .SUB,
   opAt 2952 .MLOAD,
   opAt 2953 (.Dup ⟨1, by decide⟩),
   opAt 2954 (.Dup ⟨1, by decide⟩),
   opAt 2955 .GT,
   opAt 2956 (.Swap ⟨1, by decide⟩),
   opAt 2957 .SUB,
   opAt 2958 (.Dup ⟨3, by decide⟩),
   opAt 2959 (.Dup ⟨1, by decide⟩),
   opAt 2960 .LT,
   opAt 2961 (.Swap ⟨0, by decide⟩),
   opAt 2962 (.Dup ⟨4, by decide⟩),
   opAt 2963 (.Swap ⟨0, by decide⟩),
   opAt 2964 .SUB,
   opAt 2965 (.Dup ⟨3, by decide⟩),
   opAt 2966 .MSTORE,
   opAt 2967 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2968 (.Swap ⟨1, by decide⟩),
   opAt 2969 .POP,
   pushAt 2970 1 31,
   opAt 2971 .NOT,
   opAt 2972 .ADD,
   pushAt 2973 2 4159,
   opAt 2974 (.Dup ⟨1, by decide⟩),
   opAt 2975 .GT,
   pushAt 2976 2 3957,
   opAt 2977 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
