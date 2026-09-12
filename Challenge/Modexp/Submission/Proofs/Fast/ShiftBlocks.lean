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
  [opAt 2564 .JUMPDEST,
   opAt 2565 (.Dup ⟨0, by decide⟩),
   opAt 2566 .MLOAD,
   opAt 2567 .NOT,
   opAt 2568 (.Dup ⟨2, by decide⟩),
   opAt 2569 .ADD,
   opAt 2570 (.Dup ⟨2, by decide⟩),
   opAt 2571 (.Dup ⟨1, by decide⟩),
   opAt 2572 .LT,
   opAt 2573 (.Swap ⟨2, by decide⟩),
   opAt 2574 .POP,
   opAt 2575 (.Dup ⟨1, by decide⟩),
   pushAt 2576 2 5120,
   opAt 2577 .ADD,
   opAt 2578 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2579 (.Dup ⟨0, by decide⟩),
   opAt 2580 .ISZERO,
   pushAt 2581 2 3392,
   opAt 2582 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2757 .JUMPDEST,
   opAt 2758 (.Dup ⟨0, by decide⟩),
   opAt 2759 .MLOAD,
   pushAt 2760 0 0,
   opAt 2761 .NOT,
   opAt 2762 (.Dup ⟨6, by decide⟩),
   opAt 2763 (.Dup ⟨2, by decide⟩),
   opAt 2764 .MUL,
   opAt 2765 (.Swap ⟨1, by decide⟩),
   opAt 2766 (.Dup ⟨7, by decide⟩),
   opAt 2767 .MULMOD,
   opAt 2768 (.Dup ⟨1, by decide⟩),
   opAt 2769 (.Dup ⟨1, by decide⟩),
   opAt 2770 .LT,
   opAt 2771 .SUB,
   opAt 2772 (.Dup ⟨5, by decide⟩),
   opAt 2773 (.Dup ⟨2, by decide⟩),
   opAt 2774 .ADD,
   opAt 2775 (.Dup ⟨0, by decide⟩),
   opAt 2776 (.Swap ⟨6, by decide⟩),
   opAt 2777 .GT,
   opAt 2778 .SUB,
   opAt 2779 .SUB,
   opAt 2780 (.Dup ⟨4, by decide⟩),
   opAt 2781 (.Dup ⟨3, by decide⟩),
   opAt 2782 .MLOAD,
   opAt 2783 .ADD,
   opAt 2784 (.Dup ⟨0, by decide⟩),
   opAt 2785 (.Swap ⟨5, by decide⟩),
   opAt 2786 .GT,
   opAt 2787 .ADD,
   opAt 2788 (.Swap ⟨3, by decide⟩),
   opAt 2789 (.Dup ⟨2, by decide⟩),
   opAt 2790 (.Dup ⟨4, by decide⟩),
   opAt 2791 .ADD,
   opAt 2792 (.Swap ⟨2, by decide⟩),
   opAt 2793 .MSTORE,
   opAt 2794 (.Dup ⟨2, by decide⟩),
   opAt 2795 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2796 2 8224,
   opAt 2797 (.Dup ⟨2, by decide⟩),
   opAt 2798 .GT,
   pushAt 2799 2 3618,
   opAt 2800 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2834 .JUMPDEST,
   opAt 2835 (.Dup ⟨0, by decide⟩),
   opAt 2836 .MLOAD,
   opAt 2837 (.Dup ⟨1, by decide⟩),
   pushAt 2838 2 8256,
   opAt 2839 (.Swap ⟨0, by decide⟩),
   opAt 2840 .SUB,
   opAt 2841 .MLOAD,
   opAt 2842 (.Dup ⟨1, by decide⟩),
   opAt 2843 .ADD,
   opAt 2844 (.Dup ⟨0, by decide⟩),
   opAt 2845 (.Dup ⟨2, by decide⟩),
   opAt 2846 .GT,
   opAt 2847 (.Swap ⟨1, by decide⟩),
   opAt 2848 .POP,
   opAt 2849 (.Dup ⟨3, by decide⟩),
   opAt 2850 .ADD,
   opAt 2851 (.Dup ⟨0, by decide⟩),
   opAt 2852 (.Dup ⟨4, by decide⟩),
   opAt 2853 .GT,
   opAt 2854 (.Swap ⟨3, by decide⟩),
   opAt 2855 .POP,
   opAt 2856 (.Dup ⟨2, by decide⟩),
   opAt 2857 .MSTORE,
   opAt 2858 (.Swap ⟨0, by decide⟩),
   opAt 2859 (.Swap ⟨1, by decide⟩),
   opAt 2860 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2861 (.Swap ⟨0, by decide⟩),
   pushAt 2862 1 31,
   opAt 2863 .NOT,
   opAt 2864 .ADD,
   pushAt 2865 2 8255,
   opAt 2866 (.Dup ⟨1, by decide⟩),
   opAt 2867 .GT,
   pushAt 2868 2 3707,
   opAt 2869 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2891 .JUMPDEST,
   opAt 2892 (.Dup ⟨0, by decide⟩),
   opAt 2893 .MLOAD,
   pushAt 2894 2 8256,
   opAt 2895 (.Dup ⟨2, by decide⟩),
   opAt 2896 .SUB,
   opAt 2897 .MLOAD,
   opAt 2898 (.Dup ⟨1, by decide⟩),
   opAt 2899 (.Dup ⟨1, by decide⟩),
   opAt 2900 .GT,
   opAt 2901 (.Swap ⟨1, by decide⟩),
   opAt 2902 .SUB,
   opAt 2903 (.Dup ⟨3, by decide⟩),
   opAt 2904 (.Dup ⟨1, by decide⟩),
   opAt 2905 .LT,
   opAt 2906 (.Swap ⟨0, by decide⟩),
   opAt 2907 (.Dup ⟨4, by decide⟩),
   opAt 2908 (.Swap ⟨0, by decide⟩),
   opAt 2909 .SUB,
   opAt 2910 (.Dup ⟨3, by decide⟩),
   opAt 2911 .MSTORE,
   opAt 2912 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2913 (.Swap ⟨1, by decide⟩),
   opAt 2914 .POP,
   pushAt 2915 1 31,
   opAt 2916 .NOT,
   opAt 2917 .ADD,
   pushAt 2918 2 8255,
   opAt 2919 (.Dup ⟨1, by decide⟩),
   opAt 2920 .GT,
   pushAt 2921 2 3783,
   opAt 2922 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
