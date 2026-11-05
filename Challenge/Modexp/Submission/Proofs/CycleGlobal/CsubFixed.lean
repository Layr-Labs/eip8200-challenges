import Challenge.Modexp.Submission.Proofs.CycleGlobal.PrefixPC
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.Fast
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open YulEvmCompiler

private theorem instructionPC_succ
    (p : Challenge.EvmProof.ProgramArtifact) (index : Nat) (instr : Instr)
    (hget : p.instructions[index]? = some instr) :
    p.instructionPC (index + 1) =
      p.instructionPC index + instr.bytes.length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,
    List.take_add_one, hget, Option.toList_some, assembleBytes_append,
    assembleBytes_cons, assembleBytes_nil, List.append_nil, List.length_append]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2684 2 2688,
   opAt 2685 .MLOAD,
   pushAt 2686 1 128,
   opAt 2687 .EQ,
   pushAt 2688 2 3514,
   opAt 2689 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2684 2 2688,
   opAt 2685 .MLOAD,
   pushAt 2686 1 128,
   opAt 2687 .EQ,
   pushAt 2688 2 3514,
   opAt 2689 .JUMPI,
   opAt 2652 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2690 .JUMPDEST,
   pushAt 2691 2 2336,
   opAt 2692 .MLOAD,
   pushAt 2693 1 224,
   opAt 2694 .MLOAD,
   opAt 2695 (.Dup ⟨0, by decide⟩),
   opAt 2696 (.Dup ⟨2, by decide⟩),
   opAt 2697 .SUB,
   pushAt 2698 2 2016,
   opAt 2699 .MSTORE,
   opAt 2700 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2701 (.Dup ⟨0, by decide⟩),
   pushAt 2702 1 192,
   opAt 2703 .MLOAD,
   opAt 2704 .ADD,
   opAt 2705 (.Dup ⟨0, by decide⟩),
   pushAt 2706 2 2304,
   opAt 2707 .MLOAD,
   opAt 2708 (.Dup ⟨1, by decide⟩),
   opAt 2709 (.Dup ⟨1, by decide⟩),
   opAt 2710 .SUB,
   pushAt 2711 2 1984,
   opAt 2712 .MSTORE,
   opAt 2713 .LT,
   opAt 2714 (.Swap ⟨1, by decide⟩),
   opAt 2715 .GT,
   opAt 2716 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2717 (.Dup ⟨0, by decide⟩),
   pushAt 2718 1 160,
   opAt 2719 .MLOAD,
   opAt 2720 .ADD,
   opAt 2721 (.Dup ⟨0, by decide⟩),
   pushAt 2722 2 2272,
   opAt 2723 .MLOAD,
   opAt 2724 (.Dup ⟨1, by decide⟩),
   opAt 2725 (.Dup ⟨1, by decide⟩),
   opAt 2726 .SUB,
   pushAt 2727 2 1952,
   opAt 2728 .MSTORE,
   opAt 2729 .LT,
   opAt 2730 (.Swap ⟨1, by decide⟩),
   opAt 2731 .GT,
   opAt 2732 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2733 (.Dup ⟨0, by decide⟩),
   pushAt 2734 1 128,
   opAt 2735 .MLOAD,
   opAt 2736 .ADD,
   opAt 2737 (.Dup ⟨0, by decide⟩),
   pushAt 2738 2 2240,
   opAt 2739 .MLOAD,
   opAt 2740 (.Dup ⟨1, by decide⟩),
   opAt 2741 (.Dup ⟨1, by decide⟩),
   opAt 2742 .SUB,
   pushAt 2743 2 1920,
   opAt 2744 .MSTORE,
   opAt 2745 .LT,
   opAt 2746 (.Swap ⟨1, by decide⟩),
   opAt 2747 .GT,
   opAt 2748 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2749 (.Dup ⟨0, by decide⟩),
   pushAt 2750 1 96,
   opAt 2751 .MLOAD,
   opAt 2752 .ADD,
   opAt 2753 (.Dup ⟨0, by decide⟩),
   pushAt 2754 2 2208,
   opAt 2755 .MLOAD,
   opAt 2756 (.Dup ⟨1, by decide⟩),
   opAt 2757 (.Dup ⟨1, by decide⟩),
   opAt 2758 .SUB,
   pushAt 2759 2 1888,
   opAt 2760 .MSTORE,
   opAt 2761 .LT,
   opAt 2762 (.Swap ⟨1, by decide⟩),
   opAt 2763 .GT,
   opAt 2764 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2765 .JUMPDEST,
   opAt 2766 (.Dup ⟨0, by decide⟩),
   pushAt 2767 1 64,
   opAt 2768 .MLOAD,
   opAt 2769 .ADD,
   opAt 2770 (.Dup ⟨0, by decide⟩),
   pushAt 2771 2 2176,
   opAt 2772 .MLOAD,
   opAt 2773 (.Dup ⟨1, by decide⟩),
   opAt 2774 (.Dup ⟨1, by decide⟩),
   opAt 2775 .SUB,
   pushAt 2776 2 1856,
   opAt 2777 .MSTORE,
   opAt 2778 .LT,
   opAt 2779 (.Swap ⟨1, by decide⟩),
   opAt 2780 .GT,
   opAt 2781 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2782 (.Dup ⟨0, by decide⟩),
   pushAt 2783 1 32,
   opAt 2784 .MLOAD,
   opAt 2785 .ADD,
   opAt 2786 (.Dup ⟨0, by decide⟩),
   pushAt 2787 2 2144,
   opAt 2788 .MLOAD,
   opAt 2789 (.Dup ⟨1, by decide⟩),
   opAt 2790 (.Dup ⟨1, by decide⟩),
   opAt 2791 .SUB,
   pushAt 2792 2 1824,
   opAt 2793 .MSTORE,
   opAt 2794 .LT,
   opAt 2795 (.Swap ⟨1, by decide⟩),
   opAt 2796 .GT,
   opAt 2797 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2798 (.Dup ⟨0, by decide⟩),
   pushAt 2799 0 0,
   opAt 2800 .MLOAD,
   opAt 2801 .ADD,
   opAt 2802 (.Dup ⟨0, by decide⟩),
   pushAt 2803 2 2112,
   opAt 2804 .MLOAD,
   opAt 2805 (.Dup ⟨1, by decide⟩),
   opAt 2806 (.Dup ⟨1, by decide⟩),
   opAt 2807 .SUB,
   pushAt 2808 2 1792,
   opAt 2809 .MSTORE,
   opAt 2810 .LT,
   opAt 2811 (.Swap ⟨1, by decide⟩),
   opAt 2812 .GT,
   opAt 2813 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2814 .ISZERO,
   pushAt 2815 2 2080,
   opAt 2816 .MLOAD,
   opAt 2817 .OR,
   pushAt 2818 2 3769,
   opAt 2819 .JUMPI,
   opAt 2838 .JUMPDEST,
   pushAt 2839 2 1792,
   pushAt 2840 2 2688,
   opAt 2841 .MLOAD,
   opAt 2842 (.Swap ⟨1, by decide⟩),
   opAt 2843 .MCOPY,
   opAt 2844 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2814 .ISZERO,
   pushAt 2815 2 2080,
   opAt 2816 .MLOAD,
   opAt 2817 .OR,
   pushAt 2818 2 3769,
   opAt 2819 .JUMPI,
   pushAt 2820 2 3758,
   opAt 2821 .JUMP,
   opAt 2831 .JUMPDEST,
   pushAt 2832 2 2112,
   pushAt 2833 2 2688,
   opAt 2834 .MLOAD,
   opAt 2835 (.Swap ⟨1, by decide⟩),
   opAt 2836 .MCOPY,
   opAt 2837 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2653 2 2208,
   opAt 2654 .MLOAD,
   pushAt 2655 1 96,
   opAt 2656 .MLOAD,
   opAt 2657 (.Dup ⟨0, by decide⟩),
   opAt 2658 (.Dup ⟨2, by decide⟩),
   opAt 2659 .SUB,
   pushAt 2660 2 1888,
   opAt 2661 .MSTORE,
   opAt 2662 .GT,
   pushAt 2663 2 3672,
   opAt 2664 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2765 .JUMPDEST,
   opAt 2766 (.Dup ⟨0, by decide⟩),
   pushAt 2767 1 64,
   opAt 2768 .MLOAD,
   opAt 2769 .ADD,
   opAt 2770 (.Dup ⟨0, by decide⟩),
   pushAt 2771 2 2176,
   opAt 2772 .MLOAD,
   opAt 2773 (.Dup ⟨1, by decide⟩),
   opAt 2774 (.Dup ⟨1, by decide⟩),
   opAt 2775 .SUB,
   pushAt 2776 2 1856,
   opAt 2777 .MSTORE,
   opAt 2778 .LT,
   opAt 2779 (.Swap ⟨1, by decide⟩),
   opAt 2780 .GT,
   opAt 2781 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2782 (.Dup ⟨0, by decide⟩),
   pushAt 2783 1 32,
   opAt 2784 .MLOAD,
   opAt 2785 .ADD,
   opAt 2786 (.Dup ⟨0, by decide⟩),
   pushAt 2787 2 2144,
   opAt 2788 .MLOAD,
   opAt 2789 (.Dup ⟨1, by decide⟩),
   opAt 2790 (.Dup ⟨1, by decide⟩),
   opAt 2791 .SUB,
   pushAt 2792 2 1824,
   opAt 2793 .MSTORE,
   opAt 2794 .LT,
   opAt 2795 (.Swap ⟨1, by decide⟩),
   opAt 2796 .GT,
   opAt 2797 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2798 (.Dup ⟨0, by decide⟩),
   pushAt 2799 0 0,
   opAt 2800 .MLOAD,
   opAt 2801 .ADD,
   opAt 2802 (.Dup ⟨0, by decide⟩),
   pushAt 2803 2 2112,
   opAt 2804 .MLOAD,
   opAt 2805 (.Dup ⟨1, by decide⟩),
   opAt 2806 (.Dup ⟨1, by decide⟩),
   opAt 2807 .SUB,
   pushAt 2808 2 1792,
   opAt 2809 .MSTORE,
   opAt 2810 .LT,
   opAt 2811 (.Swap ⟨1, by decide⟩),
   opAt 2812 .GT,
   opAt 2813 .OR]

@[simp] theorem cycleAnchor : CycleSubmission.Artifact.artifact.instructionPC 2643 = 3499 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3777 : CycleSubmission.Artifact.artifact.instructionPC 2679 = 3552 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3778 : CycleSubmission.Artifact.artifact.instructionPC 2820 = 3745 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3779 : CycleSubmission.Artifact.artifact.instructionPC 2821 = 3748 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3787 : CycleSubmission.Artifact.artifact.instructionPC 2822 = 3749 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3788 : CycleSubmission.Artifact.artifact.instructionPC 2827 = 3754 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3789 : CycleSubmission.Artifact.artifact.instructionPC 2828 = 3755 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3790 : CycleSubmission.Artifact.artifact.instructionPC 2829 = 3756 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3791 : CycleSubmission.Artifact.artifact.instructionPC 2830 = 3757 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3792 : CycleSubmission.Artifact.artifact.instructionPC 2831 = 3758 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3793 : CycleSubmission.Artifact.artifact.instructionPC 2832 = 3759 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3794 : CycleSubmission.Artifact.artifact.instructionPC 2833 = 3762 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3795 : CycleSubmission.Artifact.artifact.instructionPC 2834 = 3765 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3796 : CycleSubmission.Artifact.artifact.instructionPC 2835 = 3766 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3797 : CycleSubmission.Artifact.artifact.instructionPC 2836 = 3767 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3798 : CycleSubmission.Artifact.artifact.instructionPC 2836 = 3767 := fixedPC3797

@[simp] theorem fixedPC3799 : CycleSubmission.Artifact.artifact.instructionPC 2836 = 3767 := fixedPC3797

@[simp] theorem fixedPC3800 : CycleSubmission.Artifact.artifact.instructionPC 2837 = 3768 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3801 : CycleSubmission.Artifact.artifact.instructionPC 2838 = 3769 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3802 : CycleSubmission.Artifact.artifact.instructionPC 2839 = 3770 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3803 : CycleSubmission.Artifact.artifact.instructionPC 2840 = 3773 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3804 : CycleSubmission.Artifact.artifact.instructionPC 2841 = 3776 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : CycleSubmission.Artifact.artifact.instructionPC 2680 = 3553 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3115 : CycleSubmission.Artifact.artifact.instructionPC 2681 = 3554 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3116 : CycleSubmission.Artifact.artifact.instructionPC 2682 = 3555 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3117 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3558 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3118 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3561 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3119 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3564 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : CycleSubmission.Artifact.artifact.instructionPC 2649 = 3509 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3514 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2652 = 3514 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2652 (by rfl)

@[simp] theorem fixedPC3805 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3565 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3806 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3567 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3807 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3568 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3808 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3571 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPCs8 : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3572 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3809 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3573 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3810 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3576 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3811 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3577 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3812 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3579 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3813 : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3580 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3814 : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3581 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3815 : CycleSubmission.Artifact.artifact.instructionPC 2697 = 3582 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3816 : CycleSubmission.Artifact.artifact.instructionPC 2697 = 3582 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3817 : CycleSubmission.Artifact.artifact.instructionPC 2698 = 3583 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3818 : CycleSubmission.Artifact.artifact.instructionPC 2699 = 3586 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3819 : CycleSubmission.Artifact.artifact.instructionPC 2700 = 3587 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3820 : CycleSubmission.Artifact.artifact.instructionPC 2701 = 3588 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3821 : CycleSubmission.Artifact.artifact.instructionPC 2702 = 3589 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3822 : CycleSubmission.Artifact.artifact.instructionPC 2703 = 3591 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3823 : CycleSubmission.Artifact.artifact.instructionPC 2704 = 3592 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3824 : CycleSubmission.Artifact.artifact.instructionPC 2705 = 3593 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3825 : CycleSubmission.Artifact.artifact.instructionPC 2706 = 3594 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3826 : CycleSubmission.Artifact.artifact.instructionPC 2707 = 3597 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3827 : CycleSubmission.Artifact.artifact.instructionPC 2708 = 3598 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3828 : CycleSubmission.Artifact.artifact.instructionPC 2709 = 3599 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3829 : CycleSubmission.Artifact.artifact.instructionPC 2710 = 3600 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3830 : CycleSubmission.Artifact.artifact.instructionPC 2711 = 3601 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3831 : CycleSubmission.Artifact.artifact.instructionPC 2712 = 3604 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3832 : CycleSubmission.Artifact.artifact.instructionPC 2713 = 3605 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3833 : CycleSubmission.Artifact.artifact.instructionPC 2714 = 3606 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3834 : CycleSubmission.Artifact.artifact.instructionPC 2714 = 3606 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3835 : CycleSubmission.Artifact.artifact.instructionPC 2715 = 3607 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3836 : CycleSubmission.Artifact.artifact.instructionPC 2716 = 3608 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3837 : CycleSubmission.Artifact.artifact.instructionPC 2717 = 3609 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3838 : CycleSubmission.Artifact.artifact.instructionPC 2718 = 3610 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3839 : CycleSubmission.Artifact.artifact.instructionPC 2719 = 3612 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3840 : CycleSubmission.Artifact.artifact.instructionPC 2720 = 3613 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3841 : CycleSubmission.Artifact.artifact.instructionPC 2721 = 3614 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3842 : CycleSubmission.Artifact.artifact.instructionPC 2722 = 3615 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3843 : CycleSubmission.Artifact.artifact.instructionPC 2723 = 3618 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3844 : CycleSubmission.Artifact.artifact.instructionPC 2724 = 3619 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3845 : CycleSubmission.Artifact.artifact.instructionPC 2725 = 3620 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3846 : CycleSubmission.Artifact.artifact.instructionPC 2726 = 3621 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3847 : CycleSubmission.Artifact.artifact.instructionPC 2727 = 3622 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3848 : CycleSubmission.Artifact.artifact.instructionPC 2728 = 3625 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3849 : CycleSubmission.Artifact.artifact.instructionPC 2729 = 3626 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3850 : CycleSubmission.Artifact.artifact.instructionPC 2730 = 3627 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3851 : CycleSubmission.Artifact.artifact.instructionPC 2731 = 3628 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3852 : CycleSubmission.Artifact.artifact.instructionPC 2731 = 3628 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3853 : CycleSubmission.Artifact.artifact.instructionPC 2732 = 3629 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3854 : CycleSubmission.Artifact.artifact.instructionPC 2733 = 3630 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3855 : CycleSubmission.Artifact.artifact.instructionPC 2734 = 3631 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3856 : CycleSubmission.Artifact.artifact.instructionPC 2735 = 3633 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3857 : CycleSubmission.Artifact.artifact.instructionPC 2736 = 3634 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3858 : CycleSubmission.Artifact.artifact.instructionPC 2737 = 3635 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3859 : CycleSubmission.Artifact.artifact.instructionPC 2738 = 3636 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3860 : CycleSubmission.Artifact.artifact.instructionPC 2739 = 3639 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3861 : CycleSubmission.Artifact.artifact.instructionPC 2740 = 3640 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3862 : CycleSubmission.Artifact.artifact.instructionPC 2741 = 3641 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3863 : CycleSubmission.Artifact.artifact.instructionPC 2742 = 3642 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3864 : CycleSubmission.Artifact.artifact.instructionPC 2743 = 3643 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3865 : CycleSubmission.Artifact.artifact.instructionPC 2744 = 3646 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3866 : CycleSubmission.Artifact.artifact.instructionPC 2745 = 3647 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3867 : CycleSubmission.Artifact.artifact.instructionPC 2746 = 3648 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3868 : CycleSubmission.Artifact.artifact.instructionPC 2747 = 3649 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3869 : CycleSubmission.Artifact.artifact.instructionPC 2748 = 3650 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3871 : CycleSubmission.Artifact.artifact.instructionPC 2748 = 3650 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3872 : CycleSubmission.Artifact.artifact.instructionPC 2749 = 3651 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3873 : CycleSubmission.Artifact.artifact.instructionPC 2750 = 3652 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3874 : CycleSubmission.Artifact.artifact.instructionPC 2751 = 3654 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3875 : CycleSubmission.Artifact.artifact.instructionPC 2752 = 3655 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3876 : CycleSubmission.Artifact.artifact.instructionPC 2753 = 3656 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3877 : CycleSubmission.Artifact.artifact.instructionPC 2754 = 3657 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3878 : CycleSubmission.Artifact.artifact.instructionPC 2755 = 3660 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3879 : CycleSubmission.Artifact.artifact.instructionPC 2756 = 3661 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3880 : CycleSubmission.Artifact.artifact.instructionPC 2757 = 3662 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3881 : CycleSubmission.Artifact.artifact.instructionPC 2758 = 3663 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3882 : CycleSubmission.Artifact.artifact.instructionPC 2759 = 3664 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3883 : CycleSubmission.Artifact.artifact.instructionPC 2760 = 3667 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3884 : CycleSubmission.Artifact.artifact.instructionPC 2761 = 3668 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3885 : CycleSubmission.Artifact.artifact.instructionPC 2762 = 3669 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3886 : CycleSubmission.Artifact.artifact.instructionPC 2763 = 3670 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3887 : CycleSubmission.Artifact.artifact.instructionPC 2764 = 3671 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3888 : CycleSubmission.Artifact.artifact.instructionPC 2765 = 3672 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3889 : CycleSubmission.Artifact.artifact.instructionPC 2765 = 3672 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3672 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2765 = 3672 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2765 (by rfl)

@[simp] theorem fixedPC3890 : CycleSubmission.Artifact.artifact.instructionPC 2766 = 3673 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3891 : CycleSubmission.Artifact.artifact.instructionPC 2767 = 3674 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3892 : CycleSubmission.Artifact.artifact.instructionPC 2768 = 3676 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3893 : CycleSubmission.Artifact.artifact.instructionPC 2769 = 3677 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3894 : CycleSubmission.Artifact.artifact.instructionPC 2770 = 3678 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3895 : CycleSubmission.Artifact.artifact.instructionPC 2771 = 3679 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3896 : CycleSubmission.Artifact.artifact.instructionPC 2772 = 3682 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3897 : CycleSubmission.Artifact.artifact.instructionPC 2773 = 3683 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3898 : CycleSubmission.Artifact.artifact.instructionPC 2774 = 3684 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3899 : CycleSubmission.Artifact.artifact.instructionPC 2775 = 3685 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3900 : CycleSubmission.Artifact.artifact.instructionPC 2776 = 3686 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3901 : CycleSubmission.Artifact.artifact.instructionPC 2777 = 3689 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3902 : CycleSubmission.Artifact.artifact.instructionPC 2778 = 3690 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3903 : CycleSubmission.Artifact.artifact.instructionPC 2779 = 3691 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3904 : CycleSubmission.Artifact.artifact.instructionPC 2780 = 3692 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3905 : CycleSubmission.Artifact.artifact.instructionPC 2781 = 3693 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3906 : CycleSubmission.Artifact.artifact.instructionPC 2782 = 3694 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3907 : CycleSubmission.Artifact.artifact.instructionPC 2783 = 3695 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3908 : CycleSubmission.Artifact.artifact.instructionPC 2783 = 3695 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3909 : CycleSubmission.Artifact.artifact.instructionPC 2784 = 3697 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3910 : CycleSubmission.Artifact.artifact.instructionPC 2785 = 3698 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3911 : CycleSubmission.Artifact.artifact.instructionPC 2786 = 3699 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3912 : CycleSubmission.Artifact.artifact.instructionPC 2787 = 3700 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3913 : CycleSubmission.Artifact.artifact.instructionPC 2788 = 3703 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3914 : CycleSubmission.Artifact.artifact.instructionPC 2789 = 3704 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3915 : CycleSubmission.Artifact.artifact.instructionPC 2790 = 3705 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3916 : CycleSubmission.Artifact.artifact.instructionPC 2791 = 3706 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3917 : CycleSubmission.Artifact.artifact.instructionPC 2792 = 3707 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3918 : CycleSubmission.Artifact.artifact.instructionPC 2793 = 3710 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3919 : CycleSubmission.Artifact.artifact.instructionPC 2794 = 3711 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3920 : CycleSubmission.Artifact.artifact.instructionPC 2795 = 3712 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2796 = 3713 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2797 = 3714 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2798 = 3715 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2799 = 3716 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3717 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3717 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2801 = 3718 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3719 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3929 : CycleSubmission.Artifact.artifact.instructionPC 2803 = 3720 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3930 : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3723 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3931 : CycleSubmission.Artifact.artifact.instructionPC 2805 = 3724 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3932 : CycleSubmission.Artifact.artifact.instructionPC 2806 = 3725 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3933 : CycleSubmission.Artifact.artifact.instructionPC 2807 = 3726 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3934 : CycleSubmission.Artifact.artifact.instructionPC 2808 = 3727 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3935 : CycleSubmission.Artifact.artifact.instructionPC 2809 = 3730 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3936 : CycleSubmission.Artifact.artifact.instructionPC 2810 = 3731 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3937 : CycleSubmission.Artifact.artifact.instructionPC 2811 = 3732 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3938 : CycleSubmission.Artifact.artifact.instructionPC 2812 = 3733 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3939 : CycleSubmission.Artifact.artifact.instructionPC 2813 = 3734 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3940 : CycleSubmission.Artifact.artifact.instructionPC 2814 = 3735 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3941 : CycleSubmission.Artifact.artifact.instructionPC 2815 = 3736 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3942 : CycleSubmission.Artifact.artifact.instructionPC 2816 = 3739 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3943 : CycleSubmission.Artifact.artifact.instructionPC 2817 = 3740 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3944 : CycleSubmission.Artifact.artifact.instructionPC 2817 = 3740 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3945 : CycleSubmission.Artifact.artifact.instructionPC 2818 = 3741 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3946 : CycleSubmission.Artifact.artifact.instructionPC 2819 = 3744 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3947 : CycleSubmission.Artifact.artifact.instructionPC 2820 = 3745 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3948 : CycleSubmission.Artifact.artifact.instructionPC 2821 = 3748 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3949 : CycleSubmission.Artifact.artifact.instructionPC 2835 = 3766 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3950 : CycleSubmission.Artifact.artifact.instructionPC 2835 = 3766 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : CycleSubmission.Artifact.artifact.instructionPC 2836 = 3767 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3952 : CycleSubmission.Artifact.artifact.instructionPC 2837 = 3768 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3953 : CycleSubmission.Artifact.artifact.instructionPC 2838 = 3769 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3954 : CycleSubmission.Artifact.artifact.instructionPC 2839 = 3770 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3955 : CycleSubmission.Artifact.artifact.instructionPC 2840 = 3773 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3956 : CycleSubmission.Artifact.artifact.instructionPC 2841 = 3776 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3957 : CycleSubmission.Artifact.artifact.instructionPC 2842 = 3777 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3514 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2652 = 3514 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2652 (by rfl)

@[simp] theorem fixedPC4000 : CycleSubmission.Artifact.artifact.instructionPC 2649 = 3509 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4001 : CycleSubmission.Artifact.artifact.instructionPC 2650 = 3512 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4002 : CycleSubmission.Artifact.artifact.instructionPC 2651 = 3513 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4003 : CycleSubmission.Artifact.artifact.instructionPC 2652 = 3514 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4004 : CycleSubmission.Artifact.artifact.instructionPC 2653 = 3515 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4005 : CycleSubmission.Artifact.artifact.instructionPC 2654 = 3518 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4006 : CycleSubmission.Artifact.artifact.instructionPC 2655 = 3519 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4007 : CycleSubmission.Artifact.artifact.instructionPC 2656 = 3521 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4008 : CycleSubmission.Artifact.artifact.instructionPC 2657 = 3522 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4009 : CycleSubmission.Artifact.artifact.instructionPC 2658 = 3523 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4010 : CycleSubmission.Artifact.artifact.instructionPC 2659 = 3524 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4011 : CycleSubmission.Artifact.artifact.instructionPC 2660 = 3525 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4012 : CycleSubmission.Artifact.artifact.instructionPC 2661 = 3528 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2883 : CycleSubmission.Artifact.artifact.instructionPC 2627 = 3475 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : CycleSubmission.Artifact.artifact.instructionPC 2628 = 3476 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : CycleSubmission.Artifact.artifact.instructionPC 2629 = 3477 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : CycleSubmission.Artifact.artifact.instructionPC 2630 = 3478 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : CycleSubmission.Artifact.artifact.instructionPC 2631 = 3479 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : CycleSubmission.Artifact.artifact.instructionPC 2632 = 3480 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2890 : CycleSubmission.Artifact.artifact.instructionPC 2633 = 3481 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2891 : CycleSubmission.Artifact.artifact.instructionPC 2634 = 3484 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2892 : CycleSubmission.Artifact.artifact.instructionPC 2635 = 3485 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2893 : CycleSubmission.Artifact.artifact.instructionPC 2635 = 3485 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2894 : CycleSubmission.Artifact.artifact.instructionPC 2636 = 3488 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2895 : CycleSubmission.Artifact.artifact.instructionPC 2637 = 3489 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2896 : CycleSubmission.Artifact.artifact.instructionPC 2649 = 3509 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2930 : CycleSubmission.Artifact.artifact.instructionPC 2649 = 3509 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2931 : CycleSubmission.Artifact.artifact.instructionPC 2649 = 3509 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2932 : CycleSubmission.Artifact.artifact.instructionPC 2650 = 3512 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2933 : CycleSubmission.Artifact.artifact.instructionPC 2651 = 3513 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2934 : CycleSubmission.Artifact.artifact.instructionPC 2652 = 3514 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2935 : CycleSubmission.Artifact.artifact.instructionPC 2653 = 3515 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2936 : CycleSubmission.Artifact.artifact.instructionPC 2654 = 3518 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2937 : CycleSubmission.Artifact.artifact.instructionPC 2655 = 3519 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2938 : CycleSubmission.Artifact.artifact.instructionPC 2656 = 3521 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2939 : CycleSubmission.Artifact.artifact.instructionPC 2657 = 3522 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2940 : CycleSubmission.Artifact.artifact.instructionPC 2658 = 3523 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2941 : CycleSubmission.Artifact.artifact.instructionPC 2659 = 3524 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2942 : CycleSubmission.Artifact.artifact.instructionPC 2660 = 3525 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2943 : CycleSubmission.Artifact.artifact.instructionPC 2661 = 3528 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2827 = 3754 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2828 = 3755 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2829 = 3756 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2830 = 3757 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2831 = 3758 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2832 = 3759 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2833 = 3762 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2834 = 3765 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

end CycleSubmission.Global.Fast
