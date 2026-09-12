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
  [opAt 2562 .JUMPDEST,
   opAt 2563 (.Dup ⟨0, by decide⟩),
   opAt 2564 .MLOAD,
   opAt 2565 .NOT,
   opAt 2566 (.Dup ⟨2, by decide⟩),
   opAt 2567 .ADD,
   opAt 2568 (.Dup ⟨2, by decide⟩),
   opAt 2569 (.Dup ⟨1, by decide⟩),
   opAt 2570 .LT,
   opAt 2571 (.Swap ⟨2, by decide⟩),
   opAt 2572 .POP,
   opAt 2573 (.Dup ⟨1, by decide⟩),
   pushAt 2574 2 5120,
   opAt 2575 .ADD,
   opAt 2576 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2577 (.Dup ⟨0, by decide⟩),
   opAt 2578 .ISZERO,
   pushAt 2579 2 3389,
   opAt 2580 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2753 .JUMPDEST,
   opAt 2754 (.Dup ⟨0, by decide⟩),
   opAt 2755 .MLOAD,
   pushAt 2756 0 0,
   opAt 2757 .NOT,
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
   pushAt 2786 1 31,
   opAt 2787 .NOT,
   opAt 2788 .ADD,
   opAt 2789 (.Swap ⟨2, by decide⟩),
   opAt 2790 .MSTORE,
   pushAt 2791 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2792 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2793 2 8224,
   opAt 2794 (.Dup ⟨2, by decide⟩),
   opAt 2795 .GT,
   pushAt 2796 2 3612,
   opAt 2797 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2830 .JUMPDEST,
   opAt 2831 (.Dup ⟨0, by decide⟩),
   opAt 2832 .MLOAD,
   opAt 2833 (.Dup ⟨1, by decide⟩),
   pushAt 2834 2 8256,
   opAt 2835 (.Swap ⟨0, by decide⟩),
   opAt 2836 .SUB,
   opAt 2837 .MLOAD,
   opAt 2838 (.Dup ⟨1, by decide⟩),
   opAt 2839 .ADD,
   opAt 2840 (.Dup ⟨0, by decide⟩),
   opAt 2841 (.Dup ⟨2, by decide⟩),
   opAt 2842 .GT,
   opAt 2843 (.Swap ⟨1, by decide⟩),
   opAt 2844 .POP,
   opAt 2845 (.Dup ⟨3, by decide⟩),
   opAt 2846 .ADD,
   opAt 2847 (.Dup ⟨0, by decide⟩),
   opAt 2848 (.Dup ⟨4, by decide⟩),
   opAt 2849 .GT,
   opAt 2850 (.Swap ⟨3, by decide⟩),
   opAt 2851 .POP,
   opAt 2852 (.Dup ⟨2, by decide⟩),
   opAt 2853 .MSTORE,
   opAt 2854 (.Swap ⟨0, by decide⟩),
   opAt 2855 (.Swap ⟨1, by decide⟩),
   opAt 2856 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2857 (.Swap ⟨0, by decide⟩),
   pushAt 2858 1 31,
   opAt 2859 .NOT,
   opAt 2860 .ADD,
   pushAt 2861 2 8255,
   opAt 2862 (.Dup ⟨1, by decide⟩),
   opAt 2863 .GT,
   pushAt 2864 2 3734,
   opAt 2865 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2887 .JUMPDEST,
   opAt 2888 (.Dup ⟨0, by decide⟩),
   opAt 2889 .MLOAD,
   pushAt 2890 2 8256,
   opAt 2891 (.Dup ⟨2, by decide⟩),
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
   pushAt 2911 1 31,
   opAt 2912 .NOT,
   opAt 2913 .ADD,
   pushAt 2914 2 8255,
   opAt 2915 (.Dup ⟨1, by decide⟩),
   opAt 2916 .GT,
   pushAt 2917 2 3810,
   opAt 2918 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
