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
  [opAt 2566 .JUMPDEST,
   opAt 2567 (.Dup ⟨0, by decide⟩),
   opAt 2568 .MLOAD,
   opAt 2569 .NOT,
   opAt 2570 (.Dup ⟨2, by decide⟩),
   opAt 2571 .ADD,
   opAt 2572 (.Dup ⟨2, by decide⟩),
   opAt 2573 (.Dup ⟨1, by decide⟩),
   opAt 2574 .LT,
   opAt 2575 (.Swap ⟨2, by decide⟩),
   opAt 2576 .POP,
   opAt 2577 (.Dup ⟨1, by decide⟩),
   pushAt 2578 2 5120,
   opAt 2579 .ADD,
   opAt 2580 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2581 (.Dup ⟨0, by decide⟩),
   opAt 2582 .ISZERO,
   pushAt 2583 2 3647,
   opAt 2584 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2754 .JUMPDEST,
   opAt 2755 (.Dup ⟨0, by decide⟩),
   opAt 2756 .MLOAD,
   pushAt 2757 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2758 (.Dup ⟨5, by decide⟩),
   opAt 2759 (.Dup ⟨2, by decide⟩),
   opAt 2760 .MUL,
   opAt 2761 (.Swap ⟨1, by decide⟩),
   opAt 2762 (.Dup ⟨6, by decide⟩),
   opAt 2763 .MULMOD,
   opAt 2764 (.Dup ⟨1, by decide⟩),
   opAt 2765 (.Dup ⟨1, by decide⟩),
   opAt 2766 .LT,
   opAt 2767 .SUB,
   opAt 2768 (.Dup ⟨4, by decide⟩),
   opAt 2769 (.Dup ⟨2, by decide⟩),
   opAt 2770 .ADD,
   opAt 2771 (.Dup ⟨0, by decide⟩),
   opAt 2772 (.Swap ⟨5, by decide⟩),
   opAt 2773 .GT,
   opAt 2774 .SUB,
   opAt 2775 .SUB,
   opAt 2776 (.Dup ⟨3, by decide⟩),
   opAt 2777 (.Dup ⟨3, by decide⟩),
   opAt 2778 .MLOAD,
   opAt 2779 .ADD,
   opAt 2780 (.Dup ⟨0, by decide⟩),
   opAt 2781 (.Swap ⟨4, by decide⟩),
   opAt 2782 .GT,
   opAt 2783 .ADD,
   opAt 2784 (.Swap ⟨2, by decide⟩),
   opAt 2785 (.Dup ⟨2, by decide⟩),
   pushAt 2786 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2787 .ADD,
   opAt 2788 (.Swap ⟨2, by decide⟩),
   opAt 2789 .MSTORE,
   pushAt 2790 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2791 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2792 2 8224,
   opAt 2793 (.Dup ⟨2, by decide⟩),
   opAt 2794 .GT,
   pushAt 2795 2 3863,
   opAt 2796 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2829 .JUMPDEST,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   opAt 2831 .MLOAD,
   opAt 2832 (.Dup ⟨1, by decide⟩),
   pushAt 2833 2 8256,
   opAt 2834 (.Swap ⟨0, by decide⟩),
   opAt 2835 .SUB,
   opAt 2836 .MLOAD,
   opAt 2837 (.Dup ⟨1, by decide⟩),
   opAt 2838 .ADD,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   opAt 2840 (.Dup ⟨2, by decide⟩),
   opAt 2841 .GT,
   opAt 2842 (.Swap ⟨1, by decide⟩),
   opAt 2843 .POP,
   opAt 2844 (.Dup ⟨3, by decide⟩),
   opAt 2845 .ADD,
   opAt 2846 (.Dup ⟨0, by decide⟩),
   opAt 2847 (.Dup ⟨4, by decide⟩),
   opAt 2848 .GT,
   opAt 2849 (.Swap ⟨3, by decide⟩),
   opAt 2850 .POP,
   opAt 2851 (.Dup ⟨2, by decide⟩),
   opAt 2852 .MSTORE,
   opAt 2853 (.Swap ⟨0, by decide⟩),
   opAt 2854 (.Swap ⟨1, by decide⟩),
   opAt 2855 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2856 (.Swap ⟨0, by decide⟩),
   pushAt 2857 1 31, opAt 2858 .NOT,
   opAt 2859 .ADD,
   pushAt 2860 2 8255,
   opAt 2861 (.Dup ⟨1, by decide⟩),
   opAt 2862 .GT,
   pushAt 2863 2 4046,
   opAt 2864 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2886 .JUMPDEST,
   opAt 2887 (.Dup ⟨0, by decide⟩),
   opAt 2888 .MLOAD,
   opAt 2889 (.Dup ⟨1, by decide⟩),
   pushAt 2890 2 8256,
   opAt 2891 (.Swap ⟨0, by decide⟩),
   opAt 2892 .SUB,
   opAt 2893 .MLOAD,
   opAt 2894 (.Dup ⟨1, by decide⟩),
   opAt 2895 (.Dup ⟨1, by decide⟩),
   opAt 2896 .GT,
   opAt 2897 (.Swap ⟨1, by decide⟩),
   opAt 2898 .SUB,
   opAt 2899 (.Dup ⟨3, by decide⟩),
   opAt 2900 (.Dup ⟨1, by decide⟩),
   opAt 2901 .LT,
   opAt 2902 (.Swap ⟨0, by decide⟩),
   opAt 2903 (.Dup ⟨4, by decide⟩),
   opAt 2904 (.Swap ⟨0, by decide⟩),
   opAt 2905 .SUB,
   opAt 2906 (.Dup ⟨3, by decide⟩),
   opAt 2907 .MSTORE,
   opAt 2908 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2909 (.Swap ⟨1, by decide⟩),
   opAt 2910 .POP,
   pushAt 2911 1 31, opAt 2912 .NOT,
   opAt 2913 .ADD,
   pushAt 2914 2 8255,
   opAt 2915 (.Dup ⟨1, by decide⟩),
   opAt 2916 .GT,
   pushAt 2917 2 4122,
   opAt 2918 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
