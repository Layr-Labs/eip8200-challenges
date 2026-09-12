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
  [opAt 2759 .JUMPDEST,
   opAt 2760 (.Dup ⟨0, by decide⟩),
   opAt 2761 .MLOAD,
   pushAt 2762 0 0,
   opAt 2763 .NOT,
   opAt 2764 (.Dup ⟨5, by decide⟩),
   opAt 2765 (.Dup ⟨2, by decide⟩),
   opAt 2766 .MUL,
   opAt 2767 (.Swap ⟨1, by decide⟩),
   opAt 2768 (.Dup ⟨6, by decide⟩),
   opAt 2769 .MULMOD,
   opAt 2770 (.Dup ⟨1, by decide⟩),
   opAt 2771 (.Dup ⟨1, by decide⟩),
   opAt 2772 .LT,
   opAt 2773 .SUB,
   opAt 2774 (.Dup ⟨4, by decide⟩),
   opAt 2775 (.Dup ⟨2, by decide⟩),
   opAt 2776 .ADD,
   opAt 2777 (.Dup ⟨0, by decide⟩),
   opAt 2778 (.Swap ⟨5, by decide⟩),
   opAt 2779 .GT,
   opAt 2780 .SUB,
   opAt 2781 .SUB,
   opAt 2782 (.Dup ⟨3, by decide⟩),
   opAt 2783 (.Dup ⟨3, by decide⟩),
   opAt 2784 .MLOAD,
   opAt 2785 .ADD,
   opAt 2786 (.Dup ⟨0, by decide⟩),
   opAt 2787 (.Swap ⟨4, by decide⟩),
   opAt 2788 .GT,
   opAt 2789 .ADD,
   opAt 2790 (.Swap ⟨2, by decide⟩),
   opAt 2791 (.Dup ⟨2, by decide⟩),
   pushAt 2792 1 31,
   opAt 2793 .NOT,
   opAt 2794 .ADD,
   opAt 2795 (.Swap ⟨2, by decide⟩),
   opAt 2796 .MSTORE,
   pushAt 2797 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2798 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2799 2 8224,
   opAt 2800 (.Dup ⟨2, by decide⟩),
   opAt 2801 .GT,
   pushAt 2802 2 3624,
   opAt 2803 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2836 .JUMPDEST,
   opAt 2837 (.Dup ⟨0, by decide⟩),
   opAt 2838 .MLOAD,
   opAt 2839 (.Dup ⟨1, by decide⟩),
   pushAt 2840 2 8256,
   opAt 2841 (.Swap ⟨0, by decide⟩),
   opAt 2842 .SUB,
   opAt 2843 .MLOAD,
   opAt 2844 (.Dup ⟨1, by decide⟩),
   opAt 2845 .ADD,
   opAt 2846 (.Dup ⟨0, by decide⟩),
   opAt 2847 (.Dup ⟨2, by decide⟩),
   opAt 2848 .GT,
   opAt 2849 (.Swap ⟨1, by decide⟩),
   opAt 2850 .POP,
   opAt 2851 (.Dup ⟨3, by decide⟩),
   opAt 2852 .ADD,
   opAt 2853 (.Dup ⟨0, by decide⟩),
   opAt 2854 (.Dup ⟨4, by decide⟩),
   opAt 2855 .GT,
   opAt 2856 (.Swap ⟨3, by decide⟩),
   opAt 2857 .POP,
   opAt 2858 (.Dup ⟨2, by decide⟩),
   opAt 2859 .MSTORE,
   opAt 2860 (.Swap ⟨0, by decide⟩),
   opAt 2861 (.Swap ⟨1, by decide⟩),
   opAt 2862 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2863 (.Swap ⟨0, by decide⟩),
   pushAt 2864 1 31,
   opAt 2865 .NOT,
   opAt 2866 .ADD,
   pushAt 2867 2 8255,
   opAt 2868 (.Dup ⟨1, by decide⟩),
   opAt 2869 .GT,
   pushAt 2870 2 3746,
   opAt 2871 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2893 .JUMPDEST,
   opAt 2894 (.Dup ⟨0, by decide⟩),
   opAt 2895 .MLOAD,
   pushAt 2896 2 8256,
   opAt 2897 (.Dup ⟨2, by decide⟩),
   opAt 2898 .SUB,
   opAt 2899 .MLOAD,
   opAt 2900 (.Dup ⟨1, by decide⟩),
   opAt 2901 (.Dup ⟨1, by decide⟩),
   opAt 2902 .GT,
   opAt 2903 (.Swap ⟨1, by decide⟩),
   opAt 2904 .SUB,
   opAt 2905 (.Dup ⟨3, by decide⟩),
   opAt 2906 (.Dup ⟨1, by decide⟩),
   opAt 2907 .LT,
   opAt 2908 (.Swap ⟨0, by decide⟩),
   opAt 2909 (.Dup ⟨4, by decide⟩),
   opAt 2910 (.Swap ⟨0, by decide⟩),
   opAt 2911 .SUB,
   opAt 2912 (.Dup ⟨3, by decide⟩),
   opAt 2913 .MSTORE,
   opAt 2914 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2915 (.Swap ⟨1, by decide⟩),
   opAt 2916 .POP,
   pushAt 2917 1 31,
   opAt 2918 .NOT,
   opAt 2919 .ADD,
   pushAt 2920 2 8255,
   opAt 2921 (.Dup ⟨1, by decide⟩),
   opAt 2922 .GT,
   pushAt 2923 2 3822,
   opAt 2924 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
