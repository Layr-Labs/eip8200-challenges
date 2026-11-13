import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PrefixPC
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
open CycleSubmission.SharedStackArgs

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.Fast
private abbrev runtimeArtifact := CycleSubmission.Artifact.artifact
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

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2681 2 2688,
   opAt 2682 .MLOAD,
   pushAt 2683 1 128,
   opAt 2684 .EQ,
   pushAt 2685 2 4728,
   opAt 2686 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2681 2 2688,
   opAt 2682 .MLOAD,
   pushAt 2683 1 128,
   opAt 2684 .EQ,
   pushAt 2685 2 4728,
   opAt 2686 .JUMPI,
   opAt 3633 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2687 .JUMPDEST,
   pushAt 2688 2 2336,
   opAt 2689 .MLOAD,
   pushAt 2690 1 224,
   opAt 2691 .MLOAD,
   opAt 2692 (.Dup ⟨0,by decide⟩),
   opAt 2693 (.Dup ⟨2,by decide⟩),
   opAt 2694 .SUB,
   pushAt 2695 2 2016,
   opAt 2696 .MSTORE,
   opAt 2697 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2698 (.Dup ⟨0,by decide⟩),
   pushAt 2699 1 192,
   opAt 2700 .MLOAD,
   opAt 2701 .ADD,
   opAt 2702 (.Dup ⟨0,by decide⟩),
   pushAt 2703 2 2304,
   opAt 2704 .MLOAD,
   opAt 2705 (.Dup ⟨1,by decide⟩),
   opAt 2706 (.Dup ⟨1,by decide⟩),
   opAt 2707 .SUB,
   pushAt 2708 2 1984,
   opAt 2709 .MSTORE,
   opAt 2710 .LT,
   opAt 2711 (.Swap ⟨1,by decide⟩),
   opAt 2712 .GT,
   opAt 2713 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2714 (.Dup ⟨0,by decide⟩),
   pushAt 2715 1 160,
   opAt 2716 .MLOAD,
   opAt 2717 .ADD,
   opAt 2718 (.Dup ⟨0,by decide⟩),
   pushAt 2719 2 2272,
   opAt 2720 .MLOAD,
   opAt 2721 (.Dup ⟨1,by decide⟩),
   opAt 2722 (.Dup ⟨1,by decide⟩),
   opAt 2723 .SUB,
   pushAt 2724 2 1952,
   opAt 2725 .MSTORE,
   opAt 2726 .LT,
   opAt 2727 (.Swap ⟨1,by decide⟩),
   opAt 2728 .GT,
   opAt 2729 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2730 (.Dup ⟨0,by decide⟩),
   pushAt 2731 1 128,
   opAt 2732 .MLOAD,
   opAt 2733 .ADD,
   opAt 2734 (.Dup ⟨0,by decide⟩),
   pushAt 2735 2 2240,
   opAt 2736 .MLOAD,
   opAt 2737 (.Dup ⟨1,by decide⟩),
   opAt 2738 (.Dup ⟨1,by decide⟩),
   opAt 2739 .SUB,
   pushAt 2740 2 1920,
   opAt 2741 .MSTORE,
   opAt 2742 .LT,
   opAt 2743 (.Swap ⟨1,by decide⟩),
   opAt 2744 .GT,
   opAt 2745 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2746 (.Dup ⟨0,by decide⟩),
   pushAt 2747 1 96,
   opAt 2748 .MLOAD,
   opAt 2749 .ADD,
   opAt 2750 (.Dup ⟨0,by decide⟩),
   pushAt 2751 2 2208,
   opAt 2752 .MLOAD,
   opAt 2753 (.Dup ⟨1,by decide⟩),
   opAt 2754 (.Dup ⟨1,by decide⟩),
   opAt 2755 .SUB,
   pushAt 2756 2 1888,
   opAt 2757 .MSTORE,
   opAt 2758 .LT,
   opAt 2759 (.Swap ⟨1,by decide⟩),
   opAt 2760 .GT,
   opAt 2761 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2762 .JUMPDEST,
   opAt 2763 (.Dup ⟨0,by decide⟩),
   pushAt 2764 1 64,
   opAt 2765 .MLOAD,
   opAt 2766 .ADD,
   opAt 2767 (.Dup ⟨0,by decide⟩),
   pushAt 2768 2 2176,
   opAt 2769 .MLOAD,
   opAt 2770 (.Dup ⟨1,by decide⟩),
   opAt 2771 (.Dup ⟨1,by decide⟩),
   opAt 2772 .SUB,
   pushAt 2773 2 1856,
   opAt 2774 .MSTORE,
   opAt 2775 .LT,
   opAt 2776 (.Swap ⟨1,by decide⟩),
   opAt 2777 .GT,
   opAt 2778 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2779 (.Dup ⟨0,by decide⟩),
   pushAt 2780 1 32,
   opAt 2781 .MLOAD,
   opAt 2782 .ADD,
   opAt 2783 (.Dup ⟨0,by decide⟩),
   pushAt 2784 2 2144,
   opAt 2785 .MLOAD,
   opAt 2786 (.Dup ⟨1,by decide⟩),
   opAt 2787 (.Dup ⟨1,by decide⟩),
   opAt 2788 .SUB,
   pushAt 2789 2 1824,
   opAt 2790 .MSTORE,
   opAt 2791 .LT,
   opAt 2792 (.Swap ⟨1,by decide⟩),
   opAt 2793 .GT,
   opAt 2794 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2795 (.Dup ⟨0,by decide⟩),
   pushAt 2796 0 0,
   opAt 2797 .MLOAD,
   opAt 2798 .ADD,
   opAt 2799 (.Dup ⟨0,by decide⟩),
   pushAt 2800 2 2112,
   opAt 2801 .MLOAD,
   opAt 2802 (.Dup ⟨1,by decide⟩),
   opAt 2803 (.Dup ⟨1,by decide⟩),
   opAt 2804 .SUB,
   pushAt 2805 2 1792,
   opAt 2806 .MSTORE,
   opAt 2807 .LT,
   opAt 2808 (.Swap ⟨1,by decide⟩),
   opAt 2809 .GT,
   opAt 2810 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2811 .ISZERO,
   pushAt 2812 2 2080,
   opAt 2813 .MLOAD,
   opAt 2814 .OR,
   pushAt 2815 2 3687,
   opAt 2816 .JUMPI,
   opAt 2826 .JUMPDEST,
   pushAt 2827 2 1792,
   pushAt 2828 2 2688,
   opAt 2829 .MLOAD,
   opAt 2830 (.Swap ⟨1,by decide⟩),
   opAt 2831 .MCOPY,
   opAt 2832 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2811 .ISZERO,
   pushAt 2812 2 2080,
   opAt 2813 .MLOAD,
   opAt 2814 .OR,
   pushAt 2815 2 3687,
   opAt 2816 .JUMPI,
   pushAt 2817 2 3676,
   opAt 2818 .JUMP,
   opAt 2819 .JUMPDEST,
   pushAt 2820 2 2112,
   pushAt 2821 2 2688,
   opAt 2822 .MLOAD,
   opAt 2823 (.Swap ⟨1,by decide⟩),
   opAt 2824 .MCOPY,
   opAt 2825 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 3634 2 2208,
   opAt 3635 .MLOAD,
   pushAt 3636 1 96,
   opAt 3637 .MLOAD,
   opAt 3638 (.Dup ⟨0,by decide⟩),
   opAt 3639 (.Dup ⟨2,by decide⟩),
   opAt 3640 .SUB,
   pushAt 3641 2 1888,
   opAt 3642 .MSTORE,
   opAt 3643 .GT,
   pushAt 3644 2 3599,
   opAt 3645 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2762 .JUMPDEST,
   opAt 2763 (.Dup ⟨0,by decide⟩),
   pushAt 2764 1 64,
   opAt 2765 .MLOAD,
   opAt 2766 .ADD,
   opAt 2767 (.Dup ⟨0,by decide⟩),
   pushAt 2768 2 2176,
   opAt 2769 .MLOAD,
   opAt 2770 (.Dup ⟨1,by decide⟩),
   opAt 2771 (.Dup ⟨1,by decide⟩),
   opAt 2772 .SUB,
   pushAt 2773 2 1856,
   opAt 2774 .MSTORE,
   opAt 2775 .LT,
   opAt 2776 (.Swap ⟨1,by decide⟩),
   opAt 2777 .GT,
   opAt 2778 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2779 (.Dup ⟨0,by decide⟩),
   pushAt 2780 1 32,
   opAt 2781 .MLOAD,
   opAt 2782 .ADD,
   opAt 2783 (.Dup ⟨0,by decide⟩),
   pushAt 2784 2 2144,
   opAt 2785 .MLOAD,
   opAt 2786 (.Dup ⟨1,by decide⟩),
   opAt 2787 (.Dup ⟨1,by decide⟩),
   opAt 2788 .SUB,
   pushAt 2789 2 1824,
   opAt 2790 .MSTORE,
   opAt 2791 .LT,
   opAt 2792 (.Swap ⟨1,by decide⟩),
   opAt 2793 .GT,
   opAt 2794 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2795 (.Dup ⟨0,by decide⟩),
   pushAt 2796 0 0,
   opAt 2797 .MLOAD,
   opAt 2798 .ADD,
   opAt 2799 (.Dup ⟨0,by decide⟩),
   pushAt 2800 2 2112,
   opAt 2801 .MLOAD,
   opAt 2802 (.Dup ⟨1,by decide⟩),
   opAt 2803 (.Dup ⟨1,by decide⟩),
   opAt 2804 .SUB,
   pushAt 2805 2 1792,
   opAt 2806 .MSTORE,
   opAt 2807 .LT,
   opAt 2808 (.Swap ⟨1,by decide⟩),
   opAt 2809 .GT,
   opAt 2810 .OR]

@[simp] theorem cycleAnchor : runtimeArtifact.instructionPC 2634 = 3426 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3777 : runtimeArtifact.instructionPC 2676 = 3479 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3778 : runtimeArtifact.instructionPC 2817 = 3672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3779 : runtimeArtifact.instructionPC 2818 = 3675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3787 : runtimeArtifact.instructionPC 2819 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3788 : runtimeArtifact.instructionPC 2819 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3789 : runtimeArtifact.instructionPC 2819 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3790 : runtimeArtifact.instructionPC 2819 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3791 : runtimeArtifact.instructionPC 2819 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3792 : runtimeArtifact.instructionPC 2819 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3793 : runtimeArtifact.instructionPC 2820 = 3677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3794 : runtimeArtifact.instructionPC 2821 = 3680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3795 : runtimeArtifact.instructionPC 2822 = 3683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3796 : runtimeArtifact.instructionPC 2823 = 3684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3797 : runtimeArtifact.instructionPC 2824 = 3685 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3798 : runtimeArtifact.instructionPC 2824 = 3685 := fixedPC3797

@[simp] theorem fixedPC3799 : runtimeArtifact.instructionPC 2824 = 3685 := fixedPC3797

@[simp] theorem fixedPC3800 : runtimeArtifact.instructionPC 2825 = 3686 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3801 : runtimeArtifact.instructionPC 2826 = 3687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3802 : runtimeArtifact.instructionPC 2827 = 3688 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3803 : runtimeArtifact.instructionPC 2828 = 3691 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3804 : runtimeArtifact.instructionPC 2829 = 3694 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : runtimeArtifact.instructionPC 2677 = 3480 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3115 : runtimeArtifact.instructionPC 2678 = 3481 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3116 : runtimeArtifact.instructionPC 2679 = 3482 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3117 : runtimeArtifact.instructionPC 2680 = 3485 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3118 : runtimeArtifact.instructionPC 2681 = 3488 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3119 : runtimeArtifact.instructionPC 2682 = 3491 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : runtimeArtifact.instructionPC 2640 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4728 = true := by
  have h : runtimeArtifact.instructionPC 3633 = 4728 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 3633 (by rfl)

@[simp] theorem fixedPC3805 : runtimeArtifact.instructionPC 2683 = 3492 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3806 : runtimeArtifact.instructionPC 2684 = 3494 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3807 : runtimeArtifact.instructionPC 2685 = 3495 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3808 : runtimeArtifact.instructionPC 2686 = 3498 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPCs8 : runtimeArtifact.instructionPC 2687 = 3499 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3809 : runtimeArtifact.instructionPC 2688 = 3500 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3810 : runtimeArtifact.instructionPC 2689 = 3503 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3811 : runtimeArtifact.instructionPC 2690 = 3504 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3812 : runtimeArtifact.instructionPC 2691 = 3506 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3813 : runtimeArtifact.instructionPC 2692 = 3507 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3814 : runtimeArtifact.instructionPC 2693 = 3508 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3815 : runtimeArtifact.instructionPC 2694 = 3509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3816 : runtimeArtifact.instructionPC 2694 = 3509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3817 : runtimeArtifact.instructionPC 2695 = 3510 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3818 : runtimeArtifact.instructionPC 2696 = 3513 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3819 : runtimeArtifact.instructionPC 2697 = 3514 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3820 : runtimeArtifact.instructionPC 2698 = 3515 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3821 : runtimeArtifact.instructionPC 2699 = 3516 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3822 : runtimeArtifact.instructionPC 2700 = 3518 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3823 : runtimeArtifact.instructionPC 2701 = 3519 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3824 : runtimeArtifact.instructionPC 2702 = 3520 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3825 : runtimeArtifact.instructionPC 2703 = 3521 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3826 : runtimeArtifact.instructionPC 2704 = 3524 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3827 : runtimeArtifact.instructionPC 2705 = 3525 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3828 : runtimeArtifact.instructionPC 2706 = 3526 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3829 : runtimeArtifact.instructionPC 2707 = 3527 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3830 : runtimeArtifact.instructionPC 2708 = 3528 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3831 : runtimeArtifact.instructionPC 2709 = 3531 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3832 : runtimeArtifact.instructionPC 2710 = 3532 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3833 : runtimeArtifact.instructionPC 2711 = 3533 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3834 : runtimeArtifact.instructionPC 2711 = 3533 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3835 : runtimeArtifact.instructionPC 2712 = 3534 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3836 : runtimeArtifact.instructionPC 2713 = 3535 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3837 : runtimeArtifact.instructionPC 2714 = 3536 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3838 : runtimeArtifact.instructionPC 2715 = 3537 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3839 : runtimeArtifact.instructionPC 2716 = 3539 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3840 : runtimeArtifact.instructionPC 2717 = 3540 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3841 : runtimeArtifact.instructionPC 2718 = 3541 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3842 : runtimeArtifact.instructionPC 2719 = 3542 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3843 : runtimeArtifact.instructionPC 2720 = 3545 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3844 : runtimeArtifact.instructionPC 2721 = 3546 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3845 : runtimeArtifact.instructionPC 2722 = 3547 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3846 : runtimeArtifact.instructionPC 2723 = 3548 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3847 : runtimeArtifact.instructionPC 2724 = 3549 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3848 : runtimeArtifact.instructionPC 2725 = 3552 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3849 : runtimeArtifact.instructionPC 2726 = 3553 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3850 : runtimeArtifact.instructionPC 2727 = 3554 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3851 : runtimeArtifact.instructionPC 2728 = 3555 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3852 : runtimeArtifact.instructionPC 2728 = 3555 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3853 : runtimeArtifact.instructionPC 2729 = 3556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3854 : runtimeArtifact.instructionPC 2730 = 3557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3855 : runtimeArtifact.instructionPC 2731 = 3558 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3856 : runtimeArtifact.instructionPC 2732 = 3560 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3857 : runtimeArtifact.instructionPC 2733 = 3561 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3858 : runtimeArtifact.instructionPC 2734 = 3562 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3859 : runtimeArtifact.instructionPC 2735 = 3563 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3860 : runtimeArtifact.instructionPC 2736 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3861 : runtimeArtifact.instructionPC 2737 = 3567 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3862 : runtimeArtifact.instructionPC 2738 = 3568 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3863 : runtimeArtifact.instructionPC 2739 = 3569 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3864 : runtimeArtifact.instructionPC 2740 = 3570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3865 : runtimeArtifact.instructionPC 2741 = 3573 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3866 : runtimeArtifact.instructionPC 2742 = 3574 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3867 : runtimeArtifact.instructionPC 2743 = 3575 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3868 : runtimeArtifact.instructionPC 2744 = 3576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3869 : runtimeArtifact.instructionPC 2745 = 3577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3871 : runtimeArtifact.instructionPC 2745 = 3577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3872 : runtimeArtifact.instructionPC 2746 = 3578 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3873 : runtimeArtifact.instructionPC 2747 = 3579 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3874 : runtimeArtifact.instructionPC 2748 = 3581 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3875 : runtimeArtifact.instructionPC 2749 = 3582 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3876 : runtimeArtifact.instructionPC 2750 = 3583 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3877 : runtimeArtifact.instructionPC 2751 = 3584 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3878 : runtimeArtifact.instructionPC 2752 = 3587 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3879 : runtimeArtifact.instructionPC 2753 = 3588 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3880 : runtimeArtifact.instructionPC 2754 = 3589 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3881 : runtimeArtifact.instructionPC 2755 = 3590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3882 : runtimeArtifact.instructionPC 2756 = 3591 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3883 : runtimeArtifact.instructionPC 2757 = 3594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3884 : runtimeArtifact.instructionPC 2758 = 3595 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3885 : runtimeArtifact.instructionPC 2759 = 3596 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3886 : runtimeArtifact.instructionPC 2760 = 3597 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3887 : runtimeArtifact.instructionPC 2761 = 3598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3888 : runtimeArtifact.instructionPC 2762 = 3599 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3889 : runtimeArtifact.instructionPC 2762 = 3599 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3599 = true := by
  have h : runtimeArtifact.instructionPC 2762 = 3599 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2762 (by rfl)

@[simp] theorem fixedPC3890 : runtimeArtifact.instructionPC 2763 = 3600 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3891 : runtimeArtifact.instructionPC 2764 = 3601 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3892 : runtimeArtifact.instructionPC 2765 = 3603 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3893 : runtimeArtifact.instructionPC 2766 = 3604 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3894 : runtimeArtifact.instructionPC 2767 = 3605 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3895 : runtimeArtifact.instructionPC 2768 = 3606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3896 : runtimeArtifact.instructionPC 2769 = 3609 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3897 : runtimeArtifact.instructionPC 2770 = 3610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3898 : runtimeArtifact.instructionPC 2771 = 3611 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3899 : runtimeArtifact.instructionPC 2772 = 3612 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3900 : runtimeArtifact.instructionPC 2773 = 3613 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3901 : runtimeArtifact.instructionPC 2774 = 3616 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3902 : runtimeArtifact.instructionPC 2775 = 3617 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3903 : runtimeArtifact.instructionPC 2776 = 3618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3904 : runtimeArtifact.instructionPC 2777 = 3619 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3905 : runtimeArtifact.instructionPC 2778 = 3620 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3906 : runtimeArtifact.instructionPC 2779 = 3621 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3907 : runtimeArtifact.instructionPC 2780 = 3622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3908 : runtimeArtifact.instructionPC 2780 = 3622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3909 : runtimeArtifact.instructionPC 2781 = 3624 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3910 : runtimeArtifact.instructionPC 2782 = 3625 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3911 : runtimeArtifact.instructionPC 2783 = 3626 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3912 : runtimeArtifact.instructionPC 2784 = 3627 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3913 : runtimeArtifact.instructionPC 2785 = 3630 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3914 : runtimeArtifact.instructionPC 2786 = 3631 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3915 : runtimeArtifact.instructionPC 2787 = 3632 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3916 : runtimeArtifact.instructionPC 2788 = 3633 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3917 : runtimeArtifact.instructionPC 2789 = 3634 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3918 : runtimeArtifact.instructionPC 2790 = 3637 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3919 : runtimeArtifact.instructionPC 2791 = 3638 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3920 : runtimeArtifact.instructionPC 2792 = 3639 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3921 : runtimeArtifact.instructionPC 2793 = 3640 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3922 : runtimeArtifact.instructionPC 2794 = 3641 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3923 : runtimeArtifact.instructionPC 2795 = 3642 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3924 : runtimeArtifact.instructionPC 2796 = 3643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3925 : runtimeArtifact.instructionPC 2797 = 3644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3926 : runtimeArtifact.instructionPC 2797 = 3644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3927 : runtimeArtifact.instructionPC 2798 = 3645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3928 : runtimeArtifact.instructionPC 2799 = 3646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3929 : runtimeArtifact.instructionPC 2800 = 3647 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3930 : runtimeArtifact.instructionPC 2801 = 3650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3931 : runtimeArtifact.instructionPC 2802 = 3651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3932 : runtimeArtifact.instructionPC 2803 = 3652 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3933 : runtimeArtifact.instructionPC 2804 = 3653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3934 : runtimeArtifact.instructionPC 2805 = 3654 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3935 : runtimeArtifact.instructionPC 2806 = 3657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3936 : runtimeArtifact.instructionPC 2807 = 3658 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3937 : runtimeArtifact.instructionPC 2808 = 3659 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3938 : runtimeArtifact.instructionPC 2809 = 3660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3939 : runtimeArtifact.instructionPC 2810 = 3661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3940 : runtimeArtifact.instructionPC 2811 = 3662 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3941 : runtimeArtifact.instructionPC 2812 = 3663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3942 : runtimeArtifact.instructionPC 2813 = 3666 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3943 : runtimeArtifact.instructionPC 2814 = 3667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3944 : runtimeArtifact.instructionPC 2814 = 3667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3945 : runtimeArtifact.instructionPC 2815 = 3668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3946 : runtimeArtifact.instructionPC 2816 = 3671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3947 : runtimeArtifact.instructionPC 2817 = 3672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3948 : runtimeArtifact.instructionPC 2818 = 3675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3949 : runtimeArtifact.instructionPC 2823 = 3684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3950 : runtimeArtifact.instructionPC 2823 = 3684 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : runtimeArtifact.instructionPC 2824 = 3685 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3952 : runtimeArtifact.instructionPC 2825 = 3686 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3953 : runtimeArtifact.instructionPC 2826 = 3687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3954 : runtimeArtifact.instructionPC 2827 = 3688 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3955 : runtimeArtifact.instructionPC 2828 = 3691 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3956 : runtimeArtifact.instructionPC 2829 = 3694 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3957 : runtimeArtifact.instructionPC 2830 = 3695 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4728 = true := by
  have h : runtimeArtifact.instructionPC 3633 = 4728 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 3633 (by rfl)

@[simp] theorem fixedPC4000 : runtimeArtifact.instructionPC 2640 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4001 : runtimeArtifact.instructionPC 2640 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4002 : runtimeArtifact.instructionPC 2659 = 3458 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4003 : runtimeArtifact.instructionPC 3633 = 4728 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4004 : runtimeArtifact.instructionPC 3634 = 4729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4005 : runtimeArtifact.instructionPC 3635 = 4732 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4006 : runtimeArtifact.instructionPC 3636 = 4733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4007 : runtimeArtifact.instructionPC 3637 = 4735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4008 : runtimeArtifact.instructionPC 3638 = 4736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4009 : runtimeArtifact.instructionPC 3639 = 4737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4010 : runtimeArtifact.instructionPC 3640 = 4738 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4011 : runtimeArtifact.instructionPC 3641 = 4739 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4012 : runtimeArtifact.instructionPC 3642 = 4742 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2883 : runtimeArtifact.instructionPC 2618 = 3402 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2884 : runtimeArtifact.instructionPC 2619 = 3403 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2885 : runtimeArtifact.instructionPC 2620 = 3404 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2886 : runtimeArtifact.instructionPC 2621 = 3405 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2888 : runtimeArtifact.instructionPC 2622 = 3406 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2889 : runtimeArtifact.instructionPC 2623 = 3407 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2890 : runtimeArtifact.instructionPC 2624 = 3408 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2891 : runtimeArtifact.instructionPC 2625 = 3411 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2892 : runtimeArtifact.instructionPC 2626 = 3412 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2893 : runtimeArtifact.instructionPC 2626 = 3412 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2894 : runtimeArtifact.instructionPC 2627 = 3415 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2895 : runtimeArtifact.instructionPC 2628 = 3416 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2896 : runtimeArtifact.instructionPC 2640 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2930 : runtimeArtifact.instructionPC 2640 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2931 : runtimeArtifact.instructionPC 2640 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2932 : runtimeArtifact.instructionPC 2640 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2933 : runtimeArtifact.instructionPC 2659 = 3458 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2934 : runtimeArtifact.instructionPC 3633 = 4728 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2935 : runtimeArtifact.instructionPC 3634 = 4729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2936 : runtimeArtifact.instructionPC 3635 = 4732 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2937 : runtimeArtifact.instructionPC 3636 = 4733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2938 : runtimeArtifact.instructionPC 3637 = 4735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2939 : runtimeArtifact.instructionPC 3638 = 4736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2940 : runtimeArtifact.instructionPC 3639 = 4737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2941 : runtimeArtifact.instructionPC 3640 = 4738 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2942 : runtimeArtifact.instructionPC 3641 = 4739 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2943 : runtimeArtifact.instructionPC 3642 = 4742 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3921 : runtimeArtifact.instructionPC 2819 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3922 : runtimeArtifact.instructionPC 2819 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3923 : runtimeArtifact.instructionPC 2819 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3924 : runtimeArtifact.instructionPC 2819 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3925 : runtimeArtifact.instructionPC 2819 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3926 : runtimeArtifact.instructionPC 2820 = 3677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3927 : runtimeArtifact.instructionPC 2821 = 3680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3928 : runtimeArtifact.instructionPC 2822 = 3683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

end CycleSubmission.Global.Fast
