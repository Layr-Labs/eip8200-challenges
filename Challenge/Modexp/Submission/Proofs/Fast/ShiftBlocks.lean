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
  [opAt 2545 .JUMPDEST,
   opAt 2546 (.Dup ⟨0, by decide⟩),
   opAt 2547 .MLOAD,
   opAt 2548 .NOT,
   opAt 2549 (.Dup ⟨2, by decide⟩),
   opAt 2550 .ADD,
   opAt 2551 (.Dup ⟨2, by decide⟩),
   opAt 2552 (.Dup ⟨1, by decide⟩),
   opAt 2553 .LT,
   opAt 2554 (.Swap ⟨2, by decide⟩),
   opAt 2555 .POP,
   opAt 2556 (.Dup ⟨1, by decide⟩),
   pushAt 2557 2 5120,
   opAt 2558 .ADD,
   opAt 2559 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2560 (.Dup ⟨0, by decide⟩),
   opAt 2561 .ISZERO,
   pushAt 2562 2 3626,
   opAt 2563 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2728 .JUMPDEST,
   opAt 2729 (.Dup ⟨0, by decide⟩),
   opAt 2730 .MLOAD,
   pushAt 2731 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2732 (.Dup ⟨5, by decide⟩),
   opAt 2733 (.Dup ⟨2, by decide⟩),
   opAt 2734 .MUL,
   opAt 2735 (.Swap ⟨1, by decide⟩),
   opAt 2736 (.Dup ⟨6, by decide⟩),
   opAt 2737 .MULMOD,
   opAt 2738 (.Dup ⟨1, by decide⟩),
   opAt 2739 (.Dup ⟨1, by decide⟩),
   opAt 2740 .LT,
   opAt 2741 .SUB,
   opAt 2742 (.Dup ⟨4, by decide⟩),
   opAt 2743 (.Dup ⟨2, by decide⟩),
   opAt 2744 .ADD,
   opAt 2745 (.Dup ⟨0, by decide⟩),
   opAt 2746 (.Swap ⟨5, by decide⟩),
   opAt 2747 .GT,
   opAt 2748 .SUB,
   opAt 2749 .SUB,
   opAt 2750 (.Dup ⟨3, by decide⟩),
   opAt 2751 (.Dup ⟨3, by decide⟩),
   opAt 2752 .MLOAD,
   opAt 2753 .ADD,
   opAt 2754 (.Dup ⟨0, by decide⟩),
   opAt 2755 (.Swap ⟨4, by decide⟩),
   opAt 2756 .GT,
   opAt 2757 .ADD,
   opAt 2758 (.Swap ⟨2, by decide⟩),
   opAt 2759 (.Dup ⟨2, by decide⟩),
   pushAt 2760 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2761 .ADD,
   opAt 2762 (.Swap ⟨2, by decide⟩),
   opAt 2763 .MSTORE,
   pushAt 2764 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2765 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2766 2 8224,
   opAt 2767 (.Dup ⟨2, by decide⟩),
   opAt 2768 .GT,
   pushAt 2769 2 3837,
   opAt 2770 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2803 .JUMPDEST,
   opAt 2804 (.Dup ⟨0, by decide⟩),
   opAt 2805 .MLOAD,
   opAt 2806 (.Dup ⟨1, by decide⟩),
   pushAt 2807 2 8256,
   opAt 2808 (.Swap ⟨0, by decide⟩),
   opAt 2809 .SUB,
   opAt 2810 .MLOAD,
   opAt 2811 (.Dup ⟨1, by decide⟩),
   opAt 2812 .ADD,
   opAt 2813 (.Dup ⟨0, by decide⟩),
   opAt 2814 (.Dup ⟨2, by decide⟩),
   opAt 2815 .GT,
   opAt 2816 (.Swap ⟨1, by decide⟩),
   opAt 2817 .POP,
   opAt 2818 (.Dup ⟨3, by decide⟩),
   opAt 2819 .ADD,
   opAt 2820 (.Dup ⟨0, by decide⟩),
   opAt 2821 (.Dup ⟨4, by decide⟩),
   opAt 2822 .GT,
   opAt 2823 (.Swap ⟨3, by decide⟩),
   opAt 2824 .POP,
   opAt 2825 (.Dup ⟨2, by decide⟩),
   opAt 2826 .MSTORE,
   opAt 2827 (.Swap ⟨0, by decide⟩),
   opAt 2828 (.Swap ⟨1, by decide⟩),
   opAt 2829 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2830 (.Swap ⟨0, by decide⟩),
   pushAt 2831 1 31, opAt 2832 .NOT,
   opAt 2833 .ADD,
   pushAt 2834 2 8255,
   opAt 2835 (.Dup ⟨1, by decide⟩),
   opAt 2836 .GT,
   pushAt 2837 2 4020,
   opAt 2838 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2860 .JUMPDEST,
   opAt 2861 (.Dup ⟨0, by decide⟩),
   opAt 2862 .MLOAD,
   opAt 2863 (.Dup ⟨1, by decide⟩),
   pushAt 2864 2 8256,
   opAt 2865 (.Swap ⟨0, by decide⟩),
   opAt 2866 .SUB,
   opAt 2867 .MLOAD,
   opAt 2868 (.Dup ⟨1, by decide⟩),
   opAt 2869 (.Dup ⟨1, by decide⟩),
   opAt 2870 .GT,
   opAt 2871 (.Swap ⟨1, by decide⟩),
   opAt 2872 .SUB,
   opAt 2873 (.Dup ⟨3, by decide⟩),
   opAt 2874 (.Dup ⟨1, by decide⟩),
   opAt 2875 .LT,
   opAt 2876 (.Swap ⟨0, by decide⟩),
   opAt 2877 (.Dup ⟨4, by decide⟩),
   opAt 2878 (.Swap ⟨0, by decide⟩),
   opAt 2879 .SUB,
   opAt 2880 (.Dup ⟨3, by decide⟩),
   opAt 2881 .MSTORE,
   opAt 2882 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2883 (.Swap ⟨1, by decide⟩),
   opAt 2884 .POP,
   pushAt 2885 1 31, opAt 2886 .NOT,
   opAt 2887 .ADD,
   pushAt 2888 2 8255,
   opAt 2889 (.Dup ⟨1, by decide⟩),
   opAt 2890 .GT,
   pushAt 2891 2 4096,
   opAt 2892 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
