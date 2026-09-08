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
  [opAt 2550 .JUMPDEST,
   opAt 2551 (.Dup ⟨0, by decide⟩),
   opAt 2552 .MLOAD,
   opAt 2553 .NOT,
   opAt 2554 (.Dup ⟨2, by decide⟩),
   opAt 2555 .ADD,
   opAt 2556 (.Dup ⟨2, by decide⟩),
   opAt 2557 (.Dup ⟨1, by decide⟩),
   opAt 2558 .LT,
   opAt 2559 (.Swap ⟨2, by decide⟩),
   opAt 2560 .POP,
   opAt 2561 (.Dup ⟨1, by decide⟩),
   pushAt 2562 2 5120,
   opAt 2563 .ADD,
   opAt 2564 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2565 (.Dup ⟨0, by decide⟩),
   opAt 2566 .ISZERO,
   pushAt 2567 2 3647,
   opAt 2568 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2738 .JUMPDEST,
   opAt 2739 (.Dup ⟨0, by decide⟩),
   opAt 2740 .MLOAD,
   pushAt 2741 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2742 (.Dup ⟨5, by decide⟩),
   opAt 2743 (.Dup ⟨2, by decide⟩),
   opAt 2744 .MUL,
   opAt 2745 (.Swap ⟨1, by decide⟩),
   opAt 2746 (.Dup ⟨6, by decide⟩),
   opAt 2747 .MULMOD,
   opAt 2748 (.Dup ⟨1, by decide⟩),
   opAt 2749 (.Dup ⟨1, by decide⟩),
   opAt 2750 .LT,
   opAt 2751 .SUB,
   opAt 2752 (.Dup ⟨4, by decide⟩),
   opAt 2753 (.Dup ⟨2, by decide⟩),
   opAt 2754 .ADD,
   opAt 2755 (.Dup ⟨0, by decide⟩),
   opAt 2756 (.Swap ⟨5, by decide⟩),
   opAt 2757 .GT,
   opAt 2758 .SUB,
   opAt 2759 .SUB,
   opAt 2760 (.Dup ⟨3, by decide⟩),
   opAt 2761 (.Dup ⟨3, by decide⟩),
   opAt 2762 .MLOAD,
   opAt 2763 .ADD,
   opAt 2764 (.Dup ⟨0, by decide⟩),
   opAt 2765 (.Swap ⟨4, by decide⟩),
   opAt 2766 .GT,
   opAt 2767 .ADD,
   opAt 2768 (.Swap ⟨2, by decide⟩),
   opAt 2769 (.Dup ⟨2, by decide⟩),
   pushAt 2770 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2771 .ADD,
   opAt 2772 (.Swap ⟨2, by decide⟩),
   opAt 2773 .MSTORE,
   pushAt 2774 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2775 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2776 2 8224,
   opAt 2777 (.Dup ⟨2, by decide⟩),
   opAt 2778 .GT,
   pushAt 2779 2 3863,
   opAt 2780 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2813 .JUMPDEST,
   opAt 2814 (.Dup ⟨0, by decide⟩),
   opAt 2815 .MLOAD,
   opAt 2816 (.Dup ⟨1, by decide⟩),
   pushAt 2817 2 8256,
   opAt 2818 (.Swap ⟨0, by decide⟩),
   opAt 2819 .SUB,
   opAt 2820 .MLOAD,
   opAt 2821 (.Dup ⟨1, by decide⟩),
   opAt 2822 .ADD,
   opAt 2823 (.Dup ⟨0, by decide⟩),
   opAt 2824 (.Dup ⟨2, by decide⟩),
   opAt 2825 .GT,
   opAt 2826 (.Swap ⟨1, by decide⟩),
   opAt 2827 .POP,
   opAt 2828 (.Dup ⟨3, by decide⟩),
   opAt 2829 .ADD,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   opAt 2831 (.Dup ⟨4, by decide⟩),
   opAt 2832 .GT,
   opAt 2833 (.Swap ⟨3, by decide⟩),
   opAt 2834 .POP,
   opAt 2835 (.Dup ⟨2, by decide⟩),
   opAt 2836 .MSTORE,
   opAt 2837 (.Swap ⟨0, by decide⟩),
   opAt 2838 (.Swap ⟨1, by decide⟩),
   opAt 2839 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2840 (.Swap ⟨0, by decide⟩),
   pushAt 2841 1 31, opAt 2842 .NOT,
   opAt 2843 .ADD,
   pushAt 2844 2 8255,
   opAt 2845 (.Dup ⟨1, by decide⟩),
   opAt 2846 .GT,
   pushAt 2847 2 4046,
   opAt 2848 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2870 .JUMPDEST,
   opAt 2871 (.Dup ⟨0, by decide⟩),
   opAt 2872 .MLOAD,
   opAt 2873 (.Dup ⟨1, by decide⟩),
   pushAt 2874 2 8256,
   opAt 2875 (.Swap ⟨0, by decide⟩),
   opAt 2876 .SUB,
   opAt 2877 .MLOAD,
   opAt 2878 (.Dup ⟨1, by decide⟩),
   opAt 2879 (.Dup ⟨1, by decide⟩),
   opAt 2880 .GT,
   opAt 2881 (.Swap ⟨1, by decide⟩),
   opAt 2882 .SUB,
   opAt 2883 (.Dup ⟨3, by decide⟩),
   opAt 2884 (.Dup ⟨1, by decide⟩),
   opAt 2885 .LT,
   opAt 2886 (.Swap ⟨0, by decide⟩),
   opAt 2887 (.Dup ⟨4, by decide⟩),
   opAt 2888 (.Swap ⟨0, by decide⟩),
   opAt 2889 .SUB,
   opAt 2890 (.Dup ⟨3, by decide⟩),
   opAt 2891 .MSTORE,
   opAt 2892 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2893 (.Swap ⟨1, by decide⟩),
   opAt 2894 .POP,
   pushAt 2895 1 31, opAt 2896 .NOT,
   opAt 2897 .ADD,
   pushAt 2898 2 8255,
   opAt 2899 (.Dup ⟨1, by decide⟩),
   opAt 2900 .GT,
   pushAt 2901 2 4122,
   opAt 2902 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
