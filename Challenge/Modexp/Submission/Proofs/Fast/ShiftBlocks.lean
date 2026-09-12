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
   pushAt 2581 2 3395,
   opAt 2582 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2755 .JUMPDEST,
   opAt 2756 (.Dup ⟨0, by decide⟩),
   opAt 2757 .MLOAD,
   pushAt 2758 0 0,
   opAt 2759 .NOT,
   opAt 2760 (.Dup ⟨5, by decide⟩),
   opAt 2761 (.Dup ⟨2, by decide⟩),
   opAt 2762 .MUL,
   opAt 2763 (.Swap ⟨1, by decide⟩),
   opAt 2764 (.Dup ⟨6, by decide⟩),
   opAt 2765 .MULMOD,
   opAt 2766 (.Dup ⟨1, by decide⟩),
   opAt 2767 (.Dup ⟨1, by decide⟩),
   opAt 2768 .LT,
   opAt 2769 .SUB,
   opAt 2770 (.Dup ⟨4, by decide⟩),
   opAt 2771 (.Dup ⟨2, by decide⟩),
   opAt 2772 .ADD,
   opAt 2773 (.Dup ⟨0, by decide⟩),
   opAt 2774 (.Swap ⟨5, by decide⟩),
   opAt 2775 .GT,
   opAt 2776 .SUB,
   opAt 2777 .SUB,
   opAt 2778 (.Dup ⟨3, by decide⟩),
   opAt 2779 (.Dup ⟨3, by decide⟩),
   opAt 2780 .MLOAD,
   opAt 2781 .ADD,
   opAt 2782 (.Dup ⟨0, by decide⟩),
   opAt 2783 (.Swap ⟨4, by decide⟩),
   opAt 2784 .GT,
   opAt 2785 .ADD,
   opAt 2786 (.Swap ⟨2, by decide⟩),
   opAt 2787 (.Dup ⟨2, by decide⟩),
   pushAt 2788 1 31,
   opAt 2789 .NOT,
   opAt 2790 .ADD,
   opAt 2791 (.Swap ⟨2, by decide⟩),
   opAt 2792 .MSTORE,
   pushAt 2793 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2794 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2795 2 8224,
   opAt 2796 (.Dup ⟨2, by decide⟩),
   opAt 2797 .GT,
   pushAt 2798 2 3618,
   opAt 2799 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2832 .JUMPDEST,
   opAt 2833 (.Dup ⟨0, by decide⟩),
   opAt 2834 .MLOAD,
   opAt 2835 (.Dup ⟨1, by decide⟩),
   pushAt 2836 2 8256,
   opAt 2837 (.Swap ⟨0, by decide⟩),
   opAt 2838 .SUB,
   opAt 2839 .MLOAD,
   opAt 2840 (.Dup ⟨1, by decide⟩),
   opAt 2841 .ADD,
   opAt 2842 (.Dup ⟨0, by decide⟩),
   opAt 2843 (.Dup ⟨2, by decide⟩),
   opAt 2844 .GT,
   opAt 2845 (.Swap ⟨1, by decide⟩),
   opAt 2846 .POP,
   opAt 2847 (.Dup ⟨3, by decide⟩),
   opAt 2848 .ADD,
   opAt 2849 (.Dup ⟨0, by decide⟩),
   opAt 2850 (.Dup ⟨4, by decide⟩),
   opAt 2851 .GT,
   opAt 2852 (.Swap ⟨3, by decide⟩),
   opAt 2853 .POP,
   opAt 2854 (.Dup ⟨2, by decide⟩),
   opAt 2855 .MSTORE,
   opAt 2856 (.Swap ⟨0, by decide⟩),
   opAt 2857 (.Swap ⟨1, by decide⟩),
   opAt 2858 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2859 (.Swap ⟨0, by decide⟩),
   pushAt 2860 1 31,
   opAt 2861 .NOT,
   opAt 2862 .ADD,
   pushAt 2863 2 8255,
   opAt 2864 (.Dup ⟨1, by decide⟩),
   opAt 2865 .GT,
   pushAt 2866 2 3740,
   opAt 2867 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2889 .JUMPDEST,
   opAt 2890 (.Dup ⟨0, by decide⟩),
   opAt 2891 .MLOAD,
   pushAt 2892 2 8256,
   opAt 2893 (.Dup ⟨2, by decide⟩),
   opAt 2894 .SUB,
   opAt 2895 .MLOAD,
   opAt 2896 (.Dup ⟨1, by decide⟩),
   opAt 2897 (.Dup ⟨1, by decide⟩),
   opAt 2898 .GT,
   opAt 2899 (.Swap ⟨1, by decide⟩),
   opAt 2900 .SUB,
   opAt 2901 (.Dup ⟨3, by decide⟩),
   opAt 2902 (.Dup ⟨1, by decide⟩),
   opAt 2903 .LT,
   opAt 2904 (.Swap ⟨0, by decide⟩),
   opAt 2905 (.Dup ⟨4, by decide⟩),
   opAt 2906 (.Swap ⟨0, by decide⟩),
   opAt 2907 .SUB,
   opAt 2908 (.Dup ⟨3, by decide⟩),
   opAt 2909 .MSTORE,
   opAt 2910 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2911 (.Swap ⟨1, by decide⟩),
   opAt 2912 .POP,
   pushAt 2913 1 31,
   opAt 2914 .NOT,
   opAt 2915 .ADD,
   pushAt 2916 2 8255,
   opAt 2917 (.Dup ⟨1, by decide⟩),
   opAt 2918 .GT,
   pushAt 2919 2 3816,
   opAt 2920 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
