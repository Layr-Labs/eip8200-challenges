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
  [pushAt 2680 2 2688,
   opAt 2681 .MLOAD,
   pushAt 2682 1 128,
   opAt 2683 .EQ,
   pushAt 2684 2 4728,
   opAt 2685 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2680 2 2688,
   opAt 2681 .MLOAD,
   pushAt 2682 1 128,
   opAt 2683 .EQ,
   pushAt 2684 2 4728,
   opAt 2685 .JUMPI,
   opAt 3632 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2686 .JUMPDEST,
   pushAt 2687 2 2336,
   opAt 2688 .MLOAD,
   pushAt 2689 1 224,
   opAt 2690 .MLOAD,
   opAt 2691 (.Dup ⟨0,by decide⟩),
   opAt 2692 (.Dup ⟨2,by decide⟩),
   opAt 2693 .SUB,
   pushAt 2694 2 2016,
   opAt 2695 .MSTORE,
   opAt 2696 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2697 (.Dup ⟨0,by decide⟩),
   pushAt 2698 1 192,
   opAt 2699 .MLOAD,
   opAt 2700 .ADD,
   opAt 2701 (.Dup ⟨0,by decide⟩),
   pushAt 2702 2 2304,
   opAt 2703 .MLOAD,
   opAt 2704 (.Dup ⟨1,by decide⟩),
   opAt 2705 (.Dup ⟨1,by decide⟩),
   opAt 2706 .SUB,
   pushAt 2707 2 1984,
   opAt 2708 .MSTORE,
   opAt 2709 .LT,
   opAt 2710 (.Swap ⟨1,by decide⟩),
   opAt 2711 .GT,
   opAt 2712 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2713 (.Dup ⟨0,by decide⟩),
   pushAt 2714 1 160,
   opAt 2715 .MLOAD,
   opAt 2716 .ADD,
   opAt 2717 (.Dup ⟨0,by decide⟩),
   pushAt 2718 2 2272,
   opAt 2719 .MLOAD,
   opAt 2720 (.Dup ⟨1,by decide⟩),
   opAt 2721 (.Dup ⟨1,by decide⟩),
   opAt 2722 .SUB,
   pushAt 2723 2 1952,
   opAt 2724 .MSTORE,
   opAt 2725 .LT,
   opAt 2726 (.Swap ⟨1,by decide⟩),
   opAt 2727 .GT,
   opAt 2728 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2729 (.Dup ⟨0,by decide⟩),
   pushAt 2730 1 128,
   opAt 2731 .MLOAD,
   opAt 2732 .ADD,
   opAt 2733 (.Dup ⟨0,by decide⟩),
   pushAt 2734 2 2240,
   opAt 2735 .MLOAD,
   opAt 2736 (.Dup ⟨1,by decide⟩),
   opAt 2737 (.Dup ⟨1,by decide⟩),
   opAt 2738 .SUB,
   pushAt 2739 2 1920,
   opAt 2740 .MSTORE,
   opAt 2741 .LT,
   opAt 2742 (.Swap ⟨1,by decide⟩),
   opAt 2743 .GT,
   opAt 2744 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2745 (.Dup ⟨0,by decide⟩),
   pushAt 2746 1 96,
   opAt 2747 .MLOAD,
   opAt 2748 .ADD,
   opAt 2749 (.Dup ⟨0,by decide⟩),
   pushAt 2750 2 2208,
   opAt 2751 .MLOAD,
   opAt 2752 (.Dup ⟨1,by decide⟩),
   opAt 2753 (.Dup ⟨1,by decide⟩),
   opAt 2754 .SUB,
   pushAt 2755 2 1888,
   opAt 2756 .MSTORE,
   opAt 2757 .LT,
   opAt 2758 (.Swap ⟨1,by decide⟩),
   opAt 2759 .GT,
   opAt 2760 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2761 .JUMPDEST,
   opAt 2762 (.Dup ⟨0,by decide⟩),
   pushAt 2763 1 64,
   opAt 2764 .MLOAD,
   opAt 2765 .ADD,
   opAt 2766 (.Dup ⟨0,by decide⟩),
   pushAt 2767 2 2176,
   opAt 2768 .MLOAD,
   opAt 2769 (.Dup ⟨1,by decide⟩),
   opAt 2770 (.Dup ⟨1,by decide⟩),
   opAt 2771 .SUB,
   pushAt 2772 2 1856,
   opAt 2773 .MSTORE,
   opAt 2774 .LT,
   opAt 2775 (.Swap ⟨1,by decide⟩),
   opAt 2776 .GT,
   opAt 2777 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2778 (.Dup ⟨0,by decide⟩),
   pushAt 2779 1 32,
   opAt 2780 .MLOAD,
   opAt 2781 .ADD,
   opAt 2782 (.Dup ⟨0,by decide⟩),
   pushAt 2783 2 2144,
   opAt 2784 .MLOAD,
   opAt 2785 (.Dup ⟨1,by decide⟩),
   opAt 2786 (.Dup ⟨1,by decide⟩),
   opAt 2787 .SUB,
   pushAt 2788 2 1824,
   opAt 2789 .MSTORE,
   opAt 2790 .LT,
   opAt 2791 (.Swap ⟨1,by decide⟩),
   opAt 2792 .GT,
   opAt 2793 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2794 (.Dup ⟨0,by decide⟩),
   pushAt 2795 0 0,
   opAt 2796 .MLOAD,
   opAt 2797 .ADD,
   opAt 2798 (.Dup ⟨0,by decide⟩),
   pushAt 2799 2 2112,
   opAt 2800 .MLOAD,
   opAt 2801 (.Dup ⟨1,by decide⟩),
   opAt 2802 (.Dup ⟨1,by decide⟩),
   opAt 2803 .SUB,
   pushAt 2804 2 1792,
   opAt 2805 .MSTORE,
   opAt 2806 .LT,
   opAt 2807 (.Swap ⟨1,by decide⟩),
   opAt 2808 .GT,
   opAt 2809 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2810 .ISZERO,
   pushAt 2811 2 2080,
   opAt 2812 .MLOAD,
   opAt 2813 .OR,
   pushAt 2814 2 3687,
   opAt 2815 .JUMPI,
   opAt 2825 .JUMPDEST,
   pushAt 2826 2 1792,
   pushAt 2827 2 2688,
   opAt 2828 .MLOAD,
   opAt 2829 (.Swap ⟨1,by decide⟩),
   opAt 2830 .MCOPY,
   opAt 2831 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2810 .ISZERO,
   pushAt 2811 2 2080,
   opAt 2812 .MLOAD,
   opAt 2813 .OR,
   pushAt 2814 2 3687,
   opAt 2815 .JUMPI,
   pushAt 2816 2 3676,
   opAt 2817 .JUMP,
   opAt 2818 .JUMPDEST,
   pushAt 2819 2 2112,
   pushAt 2820 2 2688,
   opAt 2821 .MLOAD,
   opAt 2822 (.Swap ⟨1,by decide⟩),
   opAt 2823 .MCOPY,
   opAt 2824 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 3633 2 2208,
   opAt 3634 .MLOAD,
   pushAt 3635 1 96,
   opAt 3636 .MLOAD,
   opAt 3637 (.Dup ⟨0,by decide⟩),
   opAt 3638 (.Dup ⟨2,by decide⟩),
   opAt 3639 .SUB,
   pushAt 3640 2 1888,
   opAt 3641 .MSTORE,
   opAt 3642 .GT,
   pushAt 3643 2 3599,
   opAt 3644 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2761 .JUMPDEST,
   opAt 2762 (.Dup ⟨0,by decide⟩),
   pushAt 2763 1 64,
   opAt 2764 .MLOAD,
   opAt 2765 .ADD,
   opAt 2766 (.Dup ⟨0,by decide⟩),
   pushAt 2767 2 2176,
   opAt 2768 .MLOAD,
   opAt 2769 (.Dup ⟨1,by decide⟩),
   opAt 2770 (.Dup ⟨1,by decide⟩),
   opAt 2771 .SUB,
   pushAt 2772 2 1856,
   opAt 2773 .MSTORE,
   opAt 2774 .LT,
   opAt 2775 (.Swap ⟨1,by decide⟩),
   opAt 2776 .GT,
   opAt 2777 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2778 (.Dup ⟨0,by decide⟩),
   pushAt 2779 1 32,
   opAt 2780 .MLOAD,
   opAt 2781 .ADD,
   opAt 2782 (.Dup ⟨0,by decide⟩),
   pushAt 2783 2 2144,
   opAt 2784 .MLOAD,
   opAt 2785 (.Dup ⟨1,by decide⟩),
   opAt 2786 (.Dup ⟨1,by decide⟩),
   opAt 2787 .SUB,
   pushAt 2788 2 1824,
   opAt 2789 .MSTORE,
   opAt 2790 .LT,
   opAt 2791 (.Swap ⟨1,by decide⟩),
   opAt 2792 .GT,
   opAt 2793 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2794 (.Dup ⟨0,by decide⟩),
   pushAt 2795 0 0,
   opAt 2796 .MLOAD,
   opAt 2797 .ADD,
   opAt 2798 (.Dup ⟨0,by decide⟩),
   pushAt 2799 2 2112,
   opAt 2800 .MLOAD,
   opAt 2801 (.Dup ⟨1,by decide⟩),
   opAt 2802 (.Dup ⟨1,by decide⟩),
   opAt 2803 .SUB,
   pushAt 2804 2 1792,
   opAt 2805 .MSTORE,
   opAt 2806 .LT,
   opAt 2807 (.Swap ⟨1,by decide⟩),
   opAt 2808 .GT,
   opAt 2809 .OR]

@[simp] theorem cycleAnchor : runtimeArtifact.instructionPC 2633 = 3426 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3777 : runtimeArtifact.instructionPC 2675 = 3479 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3778 : runtimeArtifact.instructionPC 2816 = 3672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3779 : runtimeArtifact.instructionPC 2817 = 3675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3787 : runtimeArtifact.instructionPC 2818 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3788 : runtimeArtifact.instructionPC 2818 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3789 : runtimeArtifact.instructionPC 2818 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3790 : runtimeArtifact.instructionPC 2818 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3791 : runtimeArtifact.instructionPC 2818 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3792 : runtimeArtifact.instructionPC 2818 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3793 : runtimeArtifact.instructionPC 2819 = 3677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3794 : runtimeArtifact.instructionPC 2820 = 3680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3795 : runtimeArtifact.instructionPC 2821 = 3683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3796 : runtimeArtifact.instructionPC 2822 = 3684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3797 : runtimeArtifact.instructionPC 2823 = 3685 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3798 : runtimeArtifact.instructionPC 2823 = 3685 := fixedPC3797

@[simp] theorem fixedPC3799 : runtimeArtifact.instructionPC 2823 = 3685 := fixedPC3797

@[simp] theorem fixedPC3800 : runtimeArtifact.instructionPC 2824 = 3686 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3801 : runtimeArtifact.instructionPC 2825 = 3687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3802 : runtimeArtifact.instructionPC 2826 = 3688 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3803 : runtimeArtifact.instructionPC 2827 = 3691 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3804 : runtimeArtifact.instructionPC 2828 = 3694 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : runtimeArtifact.instructionPC 2676 = 3480 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3115 : runtimeArtifact.instructionPC 2677 = 3481 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3116 : runtimeArtifact.instructionPC 2678 = 3482 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3117 : runtimeArtifact.instructionPC 2679 = 3485 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3118 : runtimeArtifact.instructionPC 2680 = 3488 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3119 : runtimeArtifact.instructionPC 2681 = 3491 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : runtimeArtifact.instructionPC 2639 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4728 = true := by
  have h : runtimeArtifact.instructionPC 3632 = 4728 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 3632 (by rfl)

@[simp] theorem fixedPC3805 : runtimeArtifact.instructionPC 2682 = 3492 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3806 : runtimeArtifact.instructionPC 2683 = 3494 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3807 : runtimeArtifact.instructionPC 2684 = 3495 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3808 : runtimeArtifact.instructionPC 2685 = 3498 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPCs8 : runtimeArtifact.instructionPC 2686 = 3499 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3809 : runtimeArtifact.instructionPC 2687 = 3500 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3810 : runtimeArtifact.instructionPC 2688 = 3503 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3811 : runtimeArtifact.instructionPC 2689 = 3504 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3812 : runtimeArtifact.instructionPC 2690 = 3506 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3813 : runtimeArtifact.instructionPC 2691 = 3507 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3814 : runtimeArtifact.instructionPC 2692 = 3508 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3815 : runtimeArtifact.instructionPC 2693 = 3509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3816 : runtimeArtifact.instructionPC 2693 = 3509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3817 : runtimeArtifact.instructionPC 2694 = 3510 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3818 : runtimeArtifact.instructionPC 2695 = 3513 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3819 : runtimeArtifact.instructionPC 2696 = 3514 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3820 : runtimeArtifact.instructionPC 2697 = 3515 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3821 : runtimeArtifact.instructionPC 2698 = 3516 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3822 : runtimeArtifact.instructionPC 2699 = 3518 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3823 : runtimeArtifact.instructionPC 2700 = 3519 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3824 : runtimeArtifact.instructionPC 2701 = 3520 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3825 : runtimeArtifact.instructionPC 2702 = 3521 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3826 : runtimeArtifact.instructionPC 2703 = 3524 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3827 : runtimeArtifact.instructionPC 2704 = 3525 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3828 : runtimeArtifact.instructionPC 2705 = 3526 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3829 : runtimeArtifact.instructionPC 2706 = 3527 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3830 : runtimeArtifact.instructionPC 2707 = 3528 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3831 : runtimeArtifact.instructionPC 2708 = 3531 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3832 : runtimeArtifact.instructionPC 2709 = 3532 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3833 : runtimeArtifact.instructionPC 2710 = 3533 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3834 : runtimeArtifact.instructionPC 2710 = 3533 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3835 : runtimeArtifact.instructionPC 2711 = 3534 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3836 : runtimeArtifact.instructionPC 2712 = 3535 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3837 : runtimeArtifact.instructionPC 2713 = 3536 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3838 : runtimeArtifact.instructionPC 2714 = 3537 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3839 : runtimeArtifact.instructionPC 2715 = 3539 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3840 : runtimeArtifact.instructionPC 2716 = 3540 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3841 : runtimeArtifact.instructionPC 2717 = 3541 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3842 : runtimeArtifact.instructionPC 2718 = 3542 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3843 : runtimeArtifact.instructionPC 2719 = 3545 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3844 : runtimeArtifact.instructionPC 2720 = 3546 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3845 : runtimeArtifact.instructionPC 2721 = 3547 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3846 : runtimeArtifact.instructionPC 2722 = 3548 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3847 : runtimeArtifact.instructionPC 2723 = 3549 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3848 : runtimeArtifact.instructionPC 2724 = 3552 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3849 : runtimeArtifact.instructionPC 2725 = 3553 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3850 : runtimeArtifact.instructionPC 2726 = 3554 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3851 : runtimeArtifact.instructionPC 2727 = 3555 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3852 : runtimeArtifact.instructionPC 2727 = 3555 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3853 : runtimeArtifact.instructionPC 2728 = 3556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3854 : runtimeArtifact.instructionPC 2729 = 3557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3855 : runtimeArtifact.instructionPC 2730 = 3558 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3856 : runtimeArtifact.instructionPC 2731 = 3560 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3857 : runtimeArtifact.instructionPC 2732 = 3561 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3858 : runtimeArtifact.instructionPC 2733 = 3562 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3859 : runtimeArtifact.instructionPC 2734 = 3563 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3860 : runtimeArtifact.instructionPC 2735 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3861 : runtimeArtifact.instructionPC 2736 = 3567 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3862 : runtimeArtifact.instructionPC 2737 = 3568 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3863 : runtimeArtifact.instructionPC 2738 = 3569 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3864 : runtimeArtifact.instructionPC 2739 = 3570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3865 : runtimeArtifact.instructionPC 2740 = 3573 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3866 : runtimeArtifact.instructionPC 2741 = 3574 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3867 : runtimeArtifact.instructionPC 2742 = 3575 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3868 : runtimeArtifact.instructionPC 2743 = 3576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3869 : runtimeArtifact.instructionPC 2744 = 3577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3871 : runtimeArtifact.instructionPC 2744 = 3577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3872 : runtimeArtifact.instructionPC 2745 = 3578 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3873 : runtimeArtifact.instructionPC 2746 = 3579 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3874 : runtimeArtifact.instructionPC 2747 = 3581 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3875 : runtimeArtifact.instructionPC 2748 = 3582 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3876 : runtimeArtifact.instructionPC 2749 = 3583 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3877 : runtimeArtifact.instructionPC 2750 = 3584 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3878 : runtimeArtifact.instructionPC 2751 = 3587 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3879 : runtimeArtifact.instructionPC 2752 = 3588 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3880 : runtimeArtifact.instructionPC 2753 = 3589 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3881 : runtimeArtifact.instructionPC 2754 = 3590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3882 : runtimeArtifact.instructionPC 2755 = 3591 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3883 : runtimeArtifact.instructionPC 2756 = 3594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3884 : runtimeArtifact.instructionPC 2757 = 3595 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3885 : runtimeArtifact.instructionPC 2758 = 3596 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3886 : runtimeArtifact.instructionPC 2759 = 3597 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3887 : runtimeArtifact.instructionPC 2760 = 3598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3888 : runtimeArtifact.instructionPC 2761 = 3599 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3889 : runtimeArtifact.instructionPC 2761 = 3599 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3599 = true := by
  have h : runtimeArtifact.instructionPC 2761 = 3599 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2761 (by rfl)

@[simp] theorem fixedPC3890 : runtimeArtifact.instructionPC 2762 = 3600 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3891 : runtimeArtifact.instructionPC 2763 = 3601 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3892 : runtimeArtifact.instructionPC 2764 = 3603 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3893 : runtimeArtifact.instructionPC 2765 = 3604 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3894 : runtimeArtifact.instructionPC 2766 = 3605 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3895 : runtimeArtifact.instructionPC 2767 = 3606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3896 : runtimeArtifact.instructionPC 2768 = 3609 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3897 : runtimeArtifact.instructionPC 2769 = 3610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3898 : runtimeArtifact.instructionPC 2770 = 3611 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3899 : runtimeArtifact.instructionPC 2771 = 3612 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3900 : runtimeArtifact.instructionPC 2772 = 3613 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3901 : runtimeArtifact.instructionPC 2773 = 3616 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3902 : runtimeArtifact.instructionPC 2774 = 3617 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3903 : runtimeArtifact.instructionPC 2775 = 3618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3904 : runtimeArtifact.instructionPC 2776 = 3619 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3905 : runtimeArtifact.instructionPC 2777 = 3620 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3906 : runtimeArtifact.instructionPC 2778 = 3621 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3907 : runtimeArtifact.instructionPC 2779 = 3622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3908 : runtimeArtifact.instructionPC 2779 = 3622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3909 : runtimeArtifact.instructionPC 2780 = 3624 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3910 : runtimeArtifact.instructionPC 2781 = 3625 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3911 : runtimeArtifact.instructionPC 2782 = 3626 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3912 : runtimeArtifact.instructionPC 2783 = 3627 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3913 : runtimeArtifact.instructionPC 2784 = 3630 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3914 : runtimeArtifact.instructionPC 2785 = 3631 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3915 : runtimeArtifact.instructionPC 2786 = 3632 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3916 : runtimeArtifact.instructionPC 2787 = 3633 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3917 : runtimeArtifact.instructionPC 2788 = 3634 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3918 : runtimeArtifact.instructionPC 2789 = 3637 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3919 : runtimeArtifact.instructionPC 2790 = 3638 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3920 : runtimeArtifact.instructionPC 2791 = 3639 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3921 : runtimeArtifact.instructionPC 2792 = 3640 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3922 : runtimeArtifact.instructionPC 2793 = 3641 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3923 : runtimeArtifact.instructionPC 2794 = 3642 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3924 : runtimeArtifact.instructionPC 2795 = 3643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3925 : runtimeArtifact.instructionPC 2796 = 3644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3926 : runtimeArtifact.instructionPC 2796 = 3644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3927 : runtimeArtifact.instructionPC 2797 = 3645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3928 : runtimeArtifact.instructionPC 2798 = 3646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3929 : runtimeArtifact.instructionPC 2799 = 3647 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3930 : runtimeArtifact.instructionPC 2800 = 3650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3931 : runtimeArtifact.instructionPC 2801 = 3651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3932 : runtimeArtifact.instructionPC 2802 = 3652 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3933 : runtimeArtifact.instructionPC 2803 = 3653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3934 : runtimeArtifact.instructionPC 2804 = 3654 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3935 : runtimeArtifact.instructionPC 2805 = 3657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3936 : runtimeArtifact.instructionPC 2806 = 3658 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3937 : runtimeArtifact.instructionPC 2807 = 3659 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3938 : runtimeArtifact.instructionPC 2808 = 3660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3939 : runtimeArtifact.instructionPC 2809 = 3661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3940 : runtimeArtifact.instructionPC 2810 = 3662 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3941 : runtimeArtifact.instructionPC 2811 = 3663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3942 : runtimeArtifact.instructionPC 2812 = 3666 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3943 : runtimeArtifact.instructionPC 2813 = 3667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3944 : runtimeArtifact.instructionPC 2813 = 3667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3945 : runtimeArtifact.instructionPC 2814 = 3668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3946 : runtimeArtifact.instructionPC 2815 = 3671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3947 : runtimeArtifact.instructionPC 2816 = 3672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3948 : runtimeArtifact.instructionPC 2817 = 3675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3949 : runtimeArtifact.instructionPC 2822 = 3684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3950 : runtimeArtifact.instructionPC 2822 = 3684 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : runtimeArtifact.instructionPC 2823 = 3685 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3952 : runtimeArtifact.instructionPC 2824 = 3686 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3953 : runtimeArtifact.instructionPC 2825 = 3687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3954 : runtimeArtifact.instructionPC 2826 = 3688 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3955 : runtimeArtifact.instructionPC 2827 = 3691 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3956 : runtimeArtifact.instructionPC 2828 = 3694 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3957 : runtimeArtifact.instructionPC 2829 = 3695 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4728 = true := by
  have h : runtimeArtifact.instructionPC 3632 = 4728 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 3632 (by rfl)

@[simp] theorem fixedPC4000 : runtimeArtifact.instructionPC 2639 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4001 : runtimeArtifact.instructionPC 2639 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4002 : runtimeArtifact.instructionPC 2658 = 3458 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4003 : runtimeArtifact.instructionPC 3632 = 4728 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4004 : runtimeArtifact.instructionPC 3633 = 4729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4005 : runtimeArtifact.instructionPC 3634 = 4732 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4006 : runtimeArtifact.instructionPC 3635 = 4733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4007 : runtimeArtifact.instructionPC 3636 = 4735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4008 : runtimeArtifact.instructionPC 3637 = 4736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4009 : runtimeArtifact.instructionPC 3638 = 4737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4010 : runtimeArtifact.instructionPC 3639 = 4738 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4011 : runtimeArtifact.instructionPC 3640 = 4739 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4012 : runtimeArtifact.instructionPC 3641 = 4742 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2883 : runtimeArtifact.instructionPC 2617 = 3402 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2884 : runtimeArtifact.instructionPC 2618 = 3403 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2885 : runtimeArtifact.instructionPC 2619 = 3404 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2886 : runtimeArtifact.instructionPC 2620 = 3405 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2888 : runtimeArtifact.instructionPC 2621 = 3406 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2889 : runtimeArtifact.instructionPC 2622 = 3407 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2890 : runtimeArtifact.instructionPC 2623 = 3408 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2891 : runtimeArtifact.instructionPC 2624 = 3411 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2892 : runtimeArtifact.instructionPC 2625 = 3412 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2893 : runtimeArtifact.instructionPC 2625 = 3412 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2894 : runtimeArtifact.instructionPC 2626 = 3415 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2895 : runtimeArtifact.instructionPC 2627 = 3416 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2896 : runtimeArtifact.instructionPC 2639 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2930 : runtimeArtifact.instructionPC 2639 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2931 : runtimeArtifact.instructionPC 2639 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2932 : runtimeArtifact.instructionPC 2639 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2933 : runtimeArtifact.instructionPC 2658 = 3458 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2934 : runtimeArtifact.instructionPC 3632 = 4728 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2935 : runtimeArtifact.instructionPC 3633 = 4729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2936 : runtimeArtifact.instructionPC 3634 = 4732 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2937 : runtimeArtifact.instructionPC 3635 = 4733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2938 : runtimeArtifact.instructionPC 3636 = 4735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2939 : runtimeArtifact.instructionPC 3637 = 4736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2940 : runtimeArtifact.instructionPC 3638 = 4737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2941 : runtimeArtifact.instructionPC 3639 = 4738 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2942 : runtimeArtifact.instructionPC 3640 = 4739 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2943 : runtimeArtifact.instructionPC 3641 = 4742 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3921 : runtimeArtifact.instructionPC 2818 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3922 : runtimeArtifact.instructionPC 2818 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3923 : runtimeArtifact.instructionPC 2818 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3924 : runtimeArtifact.instructionPC 2818 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3925 : runtimeArtifact.instructionPC 2818 = 3676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3926 : runtimeArtifact.instructionPC 2819 = 3677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3927 : runtimeArtifact.instructionPC 2820 = 3680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3928 : runtimeArtifact.instructionPC 2821 = 3683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

end CycleSubmission.Global.Fast
