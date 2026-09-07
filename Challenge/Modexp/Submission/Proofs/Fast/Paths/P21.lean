import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Located paths for the appended fused `ADDMOD`/conditional-subtract routine. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Fused routine entry, instructions 2670..2685, pc 4057..4078. -/
def blk2670 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2670 .JUMPDEST,
   pushAt 2671 2 8256,
   opAt 2672 (.Dup ⟨1, by decide⟩),
   opAt 2673 .SUB,
   pushAt 2674 2 8256,
   opAt 2675 (.Dup ⟨3, by decide⟩),
   opAt 2676 .SUB,
   opAt 2677 (.Swap ⟨0, by decide⟩),
   opAt 2678 (.Swap ⟨1, by decide⟩),
   opAt 2679 .POP,
   opAt 2680 (.Swap ⟨1, by decide⟩),
   opAt 2681 .POP,
   pushAt 2682 0 0,
   pushAt 2683 0 0,
   pushAt 2684 2 9440,
   opAt 2685 .MLOAD]

/-- Fused limb loop, instructions 2686..2740, pc 4079..4142. -/
def blk2686 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2686 .JUMPDEST,
   opAt 2687 (.Dup ⟨3, by decide⟩),
   opAt 2688 (.Dup ⟨1, by decide⟩),
   opAt 2689 .ADD,
   opAt 2690 .MLOAD,
   opAt 2691 (.Dup ⟨5, by decide⟩),
   opAt 2692 (.Dup ⟨2, by decide⟩),
   opAt 2693 .ADD,
   opAt 2694 .MLOAD,
   opAt 2695 (.Dup ⟨1, by decide⟩),
   opAt 2696 .ADD,
   opAt 2697 (.Dup ⟨0, by decide⟩),
   opAt 2698 (.Swap ⟨1, by decide⟩),
   opAt 2699 .GT,
   opAt 2700 (.Dup ⟨3, by decide⟩),
   opAt 2701 (.Dup ⟨2, by decide⟩),
   opAt 2702 .ADD,
   opAt 2703 (.Dup ⟨0, by decide⟩),
   opAt 2704 (.Swap ⟨2, by decide⟩),
   opAt 2705 .GT,
   opAt 2706 .OR,
   opAt 2707 (.Swap ⟨2, by decide⟩),
   opAt 2708 .POP,
   pushAt 2709 2 8256,
   opAt 2710 (.Dup ⟨2, by decide⟩),
   opAt 2711 .SUB,
   opAt 2712 .MLOAD,
   opAt 2713 (.Dup ⟨1, by decide⟩),
   opAt 2714 .SUB,
   opAt 2715 (.Dup ⟨0, by decide⟩),
   opAt 2716 (.Dup ⟨2, by decide⟩),
   opAt 2717 .LT,
   opAt 2718 (.Dup ⟨5, by decide⟩),
   opAt 2719 (.Dup ⟨2, by decide⟩),
   opAt 2720 .SUB,
   opAt 2721 (.Dup ⟨0, by decide⟩),
   opAt 2722 (.Swap ⟨2, by decide⟩),
   opAt 2723 .LT,
   opAt 2724 .OR,
   opAt 2725 (.Swap ⟨4, by decide⟩),
   opAt 2726 .POP,
   pushAt 2727 2 1088,
   opAt 2728 (.Dup ⟨3, by decide⟩),
   opAt 2729 .SUB,
   opAt 2730 .MSTORE,
   opAt 2731 (.Dup ⟨1, by decide⟩),
   opAt 2732 .MSTORE,
   pushAt 2733 1 32,
   opAt 2734 (.Swap ⟨0, by decide⟩),
   opAt 2735 .SUB,
   pushAt 2736 2 8224,
   opAt 2737 (.Dup ⟨1, by decide⟩),
   opAt 2738 .GT,
   pushAt 2739 2 4079,
   opAt 2740 .JUMPI]

/-- Fused selection and return, instructions 2741..2763, pc 4143..4173. -/
def blk2741 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2741 (.Dup ⟨1, by decide⟩),
   pushAt 2742 2 8224,
   opAt 2743 .MSTORE,
   opAt 2744 (.Dup ⟨2, by decide⟩),
   opAt 2745 .ISZERO,
   opAt 2746 (.Dup ⟨2, by decide⟩),
   opAt 2747 .OR,
   pushAt 2748 2 1088,
   opAt 2749 .MUL,
   pushAt 2750 2 8256,
   opAt 2751 .SUB,
   pushAt 2752 2 9344,
   opAt 2753 .MLOAD,
   opAt 2754 (.Swap ⟨0, by decide⟩),
   opAt 2755 (.Dup ⟨7, by decide⟩),
   opAt 2756 .MCOPY,
   opAt 2757 .POP,
   opAt 2758 .POP,
   opAt 2759 .POP,
   opAt 2760 .POP,
   opAt 2761 .POP,
   opAt 2762 .POP,
   opAt 2763 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
