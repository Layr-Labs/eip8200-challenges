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
   pushAt 2580 2 5120,
   opAt 2581 .ADD,
   opAt 2582 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2583 (.Dup ⟨0, by decide⟩),
   opAt 2584 .ISZERO,
   pushAt 2585 2 3401,
   opAt 2586 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2761 .JUMPDEST,
   opAt 2762 (.Dup ⟨0, by decide⟩),
   opAt 2763 .MLOAD,
   pushAt 2764 0 0,
   opAt 2765 .NOT,
   opAt 2766 (.Dup ⟨6, by decide⟩),
   opAt 2767 (.Dup ⟨2, by decide⟩),
   opAt 2768 .MUL,
   opAt 2769 (.Swap ⟨1, by decide⟩),
   opAt 2770 (.Dup ⟨7, by decide⟩),
   opAt 2771 .MULMOD,
   opAt 2772 (.Dup ⟨1, by decide⟩),
   opAt 2773 (.Dup ⟨1, by decide⟩),
   opAt 2774 .LT,
   opAt 2775 .SUB,
   opAt 2776 (.Dup ⟨5, by decide⟩),
   opAt 2777 (.Dup ⟨2, by decide⟩),
   opAt 2778 .ADD,
   opAt 2779 (.Dup ⟨0, by decide⟩),
   opAt 2780 (.Swap ⟨6, by decide⟩),
   opAt 2781 .GT,
   opAt 2782 .SUB,
   opAt 2783 .SUB,
   opAt 2784 (.Dup ⟨4, by decide⟩),
   opAt 2785 (.Dup ⟨3, by decide⟩),
   opAt 2786 .MLOAD,
   opAt 2787 .ADD,
   opAt 2788 (.Dup ⟨0, by decide⟩),
   opAt 2789 (.Swap ⟨5, by decide⟩),
   opAt 2790 .GT,
   opAt 2791 .ADD,
   opAt 2792 (.Swap ⟨3, by decide⟩),
   opAt 2793 (.Dup ⟨2, by decide⟩),
   opAt 2794 (.Dup ⟨4, by decide⟩),
   opAt 2795 .ADD,
   opAt 2796 (.Swap ⟨2, by decide⟩),
   opAt 2797 .MSTORE,
   opAt 2798 (.Dup ⟨2, by decide⟩),
   opAt 2799 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2800 2 8224,
   opAt 2801 (.Dup ⟨2, by decide⟩),
   opAt 2802 .GT,
   pushAt 2803 2 3627,
   opAt 2804 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2838 .JUMPDEST,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   opAt 2840 .MLOAD,
   opAt 2841 (.Dup ⟨1, by decide⟩),
   pushAt 2842 2 8256,
   opAt 2843 (.Swap ⟨0, by decide⟩),
   opAt 2844 .SUB,
   opAt 2845 .MLOAD,
   opAt 2846 (.Dup ⟨1, by decide⟩),
   opAt 2847 .ADD,
   opAt 2848 (.Dup ⟨0, by decide⟩),
   opAt 2849 (.Dup ⟨2, by decide⟩),
   opAt 2850 .GT,
   opAt 2851 (.Swap ⟨1, by decide⟩),
   opAt 2852 .POP,
   opAt 2853 (.Dup ⟨3, by decide⟩),
   opAt 2854 .ADD,
   opAt 2855 (.Dup ⟨0, by decide⟩),
   opAt 2856 (.Dup ⟨4, by decide⟩),
   opAt 2857 .GT,
   opAt 2858 (.Swap ⟨3, by decide⟩),
   opAt 2859 .POP,
   opAt 2860 (.Dup ⟨2, by decide⟩),
   opAt 2861 .MSTORE,
   opAt 2862 (.Swap ⟨0, by decide⟩),
   opAt 2863 (.Swap ⟨1, by decide⟩),
   opAt 2864 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2865 (.Swap ⟨0, by decide⟩),
   pushAt 2866 1 31,
   opAt 2867 .NOT,
   opAt 2868 .ADD,
   pushAt 2869 2 8255,
   opAt 2870 (.Dup ⟨1, by decide⟩),
   opAt 2871 .GT,
   pushAt 2872 2 3716,
   opAt 2873 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2895 .JUMPDEST,
   opAt 2896 (.Dup ⟨0, by decide⟩),
   opAt 2897 .MLOAD,
   pushAt 2898 2 8256,
   opAt 2899 (.Dup ⟨2, by decide⟩),
   opAt 2900 .SUB,
   opAt 2901 .MLOAD,
   opAt 2902 (.Dup ⟨1, by decide⟩),
   opAt 2903 (.Dup ⟨1, by decide⟩),
   opAt 2904 .GT,
   opAt 2905 (.Swap ⟨1, by decide⟩),
   opAt 2906 .SUB,
   opAt 2907 (.Dup ⟨3, by decide⟩),
   opAt 2908 (.Dup ⟨1, by decide⟩),
   opAt 2909 .LT,
   opAt 2910 (.Swap ⟨0, by decide⟩),
   opAt 2911 (.Dup ⟨4, by decide⟩),
   opAt 2912 (.Swap ⟨0, by decide⟩),
   opAt 2913 .SUB,
   opAt 2914 (.Dup ⟨3, by decide⟩),
   opAt 2915 .MSTORE,
   opAt 2916 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2917 (.Swap ⟨1, by decide⟩),
   opAt 2918 .POP,
   pushAt 2919 1 31,
   opAt 2920 .NOT,
   opAt 2921 .ADD,
   pushAt 2922 2 8255,
   opAt 2923 (.Dup ⟨1, by decide⟩),
   opAt 2924 .GT,
   pushAt 2925 2 3792,
   opAt 2926 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
