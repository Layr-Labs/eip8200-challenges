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
  [opAt 2538 .JUMPDEST,
   opAt 2539 (.Dup ⟨0, by decide⟩),
   opAt 2540 .MLOAD,
   opAt 2541 .NOT,
   opAt 2542 (.Dup ⟨2, by decide⟩),
   opAt 2543 .ADD,
   opAt 2544 (.Dup ⟨2, by decide⟩),
   opAt 2545 (.Dup ⟨1, by decide⟩),
   opAt 2546 .LT,
   opAt 2547 (.Swap ⟨2, by decide⟩),
   opAt 2548 .POP,
   opAt 2549 (.Dup ⟨1, by decide⟩),
   pushAt 2550 2 5120,
   opAt 2551 .ADD,
   opAt 2552 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2553 (.Dup ⟨0, by decide⟩),
   opAt 2554 .ISZERO,
   pushAt 2555 2 4169,
   opAt 2556 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2726 .JUMPDEST,
   opAt 2727 (.Dup ⟨0, by decide⟩),
   opAt 2728 .MLOAD,
   pushAt 2729 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2730 (.Dup ⟨5, by decide⟩),
   opAt 2731 (.Dup ⟨2, by decide⟩),
   opAt 2732 .MUL,
   opAt 2733 (.Swap ⟨1, by decide⟩),
   opAt 2734 (.Dup ⟨6, by decide⟩),
   opAt 2735 .MULMOD,
   opAt 2736 (.Dup ⟨1, by decide⟩),
   opAt 2737 (.Dup ⟨1, by decide⟩),
   opAt 2738 .LT,
   opAt 2739 .SUB,
   opAt 2740 (.Dup ⟨4, by decide⟩),
   opAt 2741 (.Dup ⟨2, by decide⟩),
   opAt 2742 .ADD,
   opAt 2743 (.Dup ⟨0, by decide⟩),
   opAt 2744 (.Swap ⟨5, by decide⟩),
   opAt 2745 .GT,
   opAt 2746 .SUB,
   opAt 2747 .SUB,
   opAt 2748 (.Dup ⟨3, by decide⟩),
   opAt 2749 (.Dup ⟨3, by decide⟩),
   opAt 2750 .MLOAD,
   opAt 2751 .ADD,
   opAt 2752 (.Dup ⟨0, by decide⟩),
   opAt 2753 (.Swap ⟨4, by decide⟩),
   opAt 2754 .GT,
   opAt 2755 .ADD,
   opAt 2756 (.Swap ⟨2, by decide⟩),
   opAt 2757 (.Dup ⟨2, by decide⟩),
   pushAt 2758 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2759 .ADD,
   opAt 2760 (.Swap ⟨2, by decide⟩),
   opAt 2761 .MSTORE,
   pushAt 2762 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2763 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2764 2 8224,
   opAt 2765 (.Dup ⟨2, by decide⟩),
   opAt 2766 .GT,
   pushAt 2767 2 4386,
   opAt 2768 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2801 .JUMPDEST,
   opAt 2802 (.Dup ⟨0, by decide⟩),
   opAt 2803 .MLOAD,
   opAt 2804 (.Dup ⟨1, by decide⟩),
   pushAt 2805 2 8256,
   opAt 2806 (.Swap ⟨0, by decide⟩),
   opAt 2807 .SUB,
   opAt 2808 .MLOAD,
   opAt 2809 (.Dup ⟨1, by decide⟩),
   opAt 2810 .ADD,
   opAt 2811 (.Dup ⟨0, by decide⟩),
   opAt 2812 (.Dup ⟨2, by decide⟩),
   opAt 2813 .GT,
   opAt 2814 (.Swap ⟨1, by decide⟩),
   opAt 2815 .POP,
   opAt 2816 (.Dup ⟨3, by decide⟩),
   opAt 2817 .ADD,
   opAt 2818 (.Dup ⟨0, by decide⟩),
   opAt 2819 (.Dup ⟨4, by decide⟩),
   opAt 2820 .GT,
   opAt 2821 (.Swap ⟨3, by decide⟩),
   opAt 2822 .POP,
   opAt 2823 (.Dup ⟨2, by decide⟩),
   opAt 2824 .MSTORE,
   opAt 2825 (.Swap ⟨0, by decide⟩),
   opAt 2826 (.Swap ⟨1, by decide⟩),
   opAt 2827 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2828 (.Swap ⟨0, by decide⟩),
   pushAt 2829 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2830 .ADD,
   pushAt 2831 2 8255,
   opAt 2832 (.Dup ⟨1, by decide⟩),
   opAt 2833 .GT,
   pushAt 2834 2 4569,
   opAt 2835 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2857 .JUMPDEST,
   opAt 2858 (.Dup ⟨0, by decide⟩),
   opAt 2859 .MLOAD,
   opAt 2860 (.Dup ⟨1, by decide⟩),
   pushAt 2861 2 8256,
   opAt 2862 (.Swap ⟨0, by decide⟩),
   opAt 2863 .SUB,
   opAt 2864 .MLOAD,
   opAt 2865 (.Dup ⟨1, by decide⟩),
   opAt 2866 (.Dup ⟨1, by decide⟩),
   opAt 2867 .GT,
   opAt 2868 (.Swap ⟨1, by decide⟩),
   opAt 2869 .SUB,
   opAt 2870 (.Dup ⟨3, by decide⟩),
   opAt 2871 (.Dup ⟨1, by decide⟩),
   opAt 2872 .LT,
   opAt 2873 (.Swap ⟨0, by decide⟩),
   opAt 2874 (.Dup ⟨4, by decide⟩),
   opAt 2875 (.Swap ⟨0, by decide⟩),
   opAt 2876 .SUB,
   opAt 2877 (.Dup ⟨3, by decide⟩),
   opAt 2878 .MSTORE,
   opAt 2879 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2880 (.Swap ⟨1, by decide⟩),
   opAt 2881 .POP,
   pushAt 2882 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2883 .ADD,
   pushAt 2884 2 8255,
   opAt 2885 (.Dup ⟨1, by decide⟩),
   opAt 2886 .GT,
   pushAt 2887 2 4675,
   opAt 2888 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
