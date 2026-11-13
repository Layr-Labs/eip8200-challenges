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
  [pushAt 2652 2 2688,
   opAt 2653 .MLOAD,
   pushAt 2654 1 128,
   opAt 2655 .EQ,
   pushAt 2656 2 4605,
   opAt 2657 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2652 2 2688,
   opAt 2653 .MLOAD,
   pushAt 2654 1 128,
   opAt 2655 .EQ,
   pushAt 2656 2 4605,
   opAt 2657 .JUMPI,
   opAt 3597 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2658 2 2336,
   opAt 2659 .MLOAD,
   pushAt 2660 1 224,
   opAt 2661 .MLOAD,
   opAt 2662 (.Dup ⟨0,by decide⟩),
   opAt 2663 (.Dup ⟨2,by decide⟩),
   opAt 2664 .SUB,
   pushAt 2665 2 2016,
   opAt 2666 .MSTORE,
   opAt 2667 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2668 (.Dup ⟨0,by decide⟩),
   pushAt 2669 1 192,
   opAt 2670 .MLOAD,
   opAt 2671 .ADD,
   opAt 2672 (.Dup ⟨0,by decide⟩),
   pushAt 2673 2 2304,
   opAt 2674 .MLOAD,
   opAt 2675 (.Dup ⟨1,by decide⟩),
   opAt 2676 (.Dup ⟨1,by decide⟩),
   opAt 2677 .SUB,
   pushAt 2678 2 1984,
   opAt 2679 .MSTORE,
   opAt 2680 .LT,
   opAt 2681 (.Swap ⟨1,by decide⟩),
   opAt 2682 .GT,
   opAt 2683 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2684 (.Dup ⟨0,by decide⟩),
   pushAt 2685 1 160,
   opAt 2686 .MLOAD,
   opAt 2687 .ADD,
   opAt 2688 (.Dup ⟨0,by decide⟩),
   pushAt 2689 2 2272,
   opAt 2690 .MLOAD,
   opAt 2691 (.Dup ⟨1,by decide⟩),
   opAt 2692 (.Dup ⟨1,by decide⟩),
   opAt 2693 .SUB,
   pushAt 2694 2 1952,
   opAt 2695 .MSTORE,
   opAt 2696 .LT,
   opAt 2697 (.Swap ⟨1,by decide⟩),
   opAt 2698 .GT,
   opAt 2699 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2700 (.Dup ⟨0,by decide⟩),
   pushAt 2701 1 128,
   opAt 2702 .MLOAD,
   opAt 2703 .ADD,
   opAt 2704 (.Dup ⟨0,by decide⟩),
   pushAt 2705 2 2240,
   opAt 2706 .MLOAD,
   opAt 2707 (.Dup ⟨1,by decide⟩),
   opAt 2708 (.Dup ⟨1,by decide⟩),
   opAt 2709 .SUB,
   pushAt 2710 2 1920,
   opAt 2711 .MSTORE,
   opAt 2712 .LT,
   opAt 2713 (.Swap ⟨1,by decide⟩),
   opAt 2714 .GT,
   opAt 2715 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2716 (.Dup ⟨0,by decide⟩),
   pushAt 2717 1 96,
   opAt 2718 .MLOAD,
   opAt 2719 .ADD,
   opAt 2720 (.Dup ⟨0,by decide⟩),
   pushAt 2721 2 2208,
   opAt 2722 .MLOAD,
   opAt 2723 (.Dup ⟨1,by decide⟩),
   opAt 2724 (.Dup ⟨1,by decide⟩),
   opAt 2725 .SUB,
   pushAt 2726 2 1888,
   opAt 2727 .MSTORE,
   opAt 2728 .LT,
   opAt 2729 (.Swap ⟨1,by decide⟩),
   opAt 2730 .GT,
   opAt 2731 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2732 .JUMPDEST,
   opAt 2733 (.Dup ⟨0,by decide⟩),
   pushAt 2734 1 64,
   opAt 2735 .MLOAD,
   opAt 2736 .ADD,
   opAt 2737 (.Dup ⟨0,by decide⟩),
   pushAt 2738 2 2176,
   opAt 2739 .MLOAD,
   opAt 2740 (.Dup ⟨1,by decide⟩),
   opAt 2741 (.Dup ⟨1,by decide⟩),
   opAt 2742 .SUB,
   pushAt 2743 2 1856,
   opAt 2744 .MSTORE,
   opAt 2745 .LT,
   opAt 2746 (.Swap ⟨1,by decide⟩),
   opAt 2747 .GT,
   opAt 2748 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2749 (.Dup ⟨0,by decide⟩),
   pushAt 2750 1 32,
   opAt 2751 .MLOAD,
   opAt 2752 .ADD,
   opAt 2753 (.Dup ⟨0,by decide⟩),
   pushAt 2754 2 2144,
   opAt 2755 .MLOAD,
   opAt 2756 (.Dup ⟨1,by decide⟩),
   opAt 2757 (.Dup ⟨1,by decide⟩),
   opAt 2758 .SUB,
   pushAt 2759 2 1824,
   opAt 2760 .MSTORE,
   opAt 2761 .LT,
   opAt 2762 (.Swap ⟨1,by decide⟩),
   opAt 2763 .GT,
   opAt 2764 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2765 (.Dup ⟨0,by decide⟩),
   pushAt 2766 0 0,
   opAt 2767 .MLOAD,
   opAt 2768 .ADD,
   opAt 2769 (.Dup ⟨0,by decide⟩),
   pushAt 2770 2 2112,
   opAt 2771 .MLOAD,
   opAt 2772 (.Dup ⟨1,by decide⟩),
   opAt 2773 (.Dup ⟨1,by decide⟩),
   opAt 2774 .SUB,
   pushAt 2775 2 1792,
   opAt 2776 .MSTORE,
   opAt 2777 .LT,
   opAt 2778 (.Swap ⟨1,by decide⟩),
   opAt 2779 .GT,
   opAt 2780 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2781 .ISZERO,
   pushAt 2782 2 2080,
   opAt 2783 .MLOAD,
   opAt 2784 .OR,
   pushAt 2785 2 3577,
   opAt 2786 .JUMPI,
   opAt 2796 .JUMPDEST,
   pushAt 2797 2 1792,
   pushAt 2798 2 2688,
   opAt 2799 .MLOAD,
   opAt 2800 (.Swap ⟨1,by decide⟩),
   opAt 2801 .MCOPY,
   opAt 2802 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2781 .ISZERO,
   pushAt 2782 2 2080,
   opAt 2783 .MLOAD,
   opAt 2784 .OR,
   pushAt 2785 2 3577,
   opAt 2786 .JUMPI,
   pushAt 2787 2 3566,
   opAt 2788 .JUMP,
   opAt 2789 .JUMPDEST,
   pushAt 2790 2 2112,
   pushAt 2791 2 2688,
   opAt 2792 .MLOAD,
   opAt 2793 (.Swap ⟨1,by decide⟩),
   opAt 2794 .MCOPY,
   opAt 2795 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 3598 2 2208,
   opAt 3599 .MLOAD,
   pushAt 3600 1 96,
   opAt 3601 .MLOAD,
   opAt 3602 (.Dup ⟨0,by decide⟩),
   opAt 3603 (.Dup ⟨2,by decide⟩),
   opAt 3604 .SUB,
   pushAt 3605 2 1888,
   opAt 3606 .MSTORE,
   opAt 3607 .GT,
   pushAt 3608 2 3489,
   opAt 3609 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2732 .JUMPDEST,
   opAt 2733 (.Dup ⟨0,by decide⟩),
   pushAt 2734 1 64,
   opAt 2735 .MLOAD,
   opAt 2736 .ADD,
   opAt 2737 (.Dup ⟨0,by decide⟩),
   pushAt 2738 2 2176,
   opAt 2739 .MLOAD,
   opAt 2740 (.Dup ⟨1,by decide⟩),
   opAt 2741 (.Dup ⟨1,by decide⟩),
   opAt 2742 .SUB,
   pushAt 2743 2 1856,
   opAt 2744 .MSTORE,
   opAt 2745 .LT,
   opAt 2746 (.Swap ⟨1,by decide⟩),
   opAt 2747 .GT,
   opAt 2748 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2749 (.Dup ⟨0,by decide⟩),
   pushAt 2750 1 32,
   opAt 2751 .MLOAD,
   opAt 2752 .ADD,
   opAt 2753 (.Dup ⟨0,by decide⟩),
   pushAt 2754 2 2144,
   opAt 2755 .MLOAD,
   opAt 2756 (.Dup ⟨1,by decide⟩),
   opAt 2757 (.Dup ⟨1,by decide⟩),
   opAt 2758 .SUB,
   pushAt 2759 2 1824,
   opAt 2760 .MSTORE,
   opAt 2761 .LT,
   opAt 2762 (.Swap ⟨1,by decide⟩),
   opAt 2763 .GT,
   opAt 2764 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2765 (.Dup ⟨0,by decide⟩),
   pushAt 2766 0 0,
   opAt 2767 .MLOAD,
   opAt 2768 .ADD,
   opAt 2769 (.Dup ⟨0,by decide⟩),
   pushAt 2770 2 2112,
   opAt 2771 .MLOAD,
   opAt 2772 (.Dup ⟨1,by decide⟩),
   opAt 2773 (.Dup ⟨1,by decide⟩),
   opAt 2774 .SUB,
   pushAt 2775 2 1792,
   opAt 2776 .MSTORE,
   opAt 2777 .LT,
   opAt 2778 (.Swap ⟨1,by decide⟩),
   opAt 2779 .GT,
   opAt 2780 .OR]

@[simp] theorem cycleAnchor : runtimeArtifact.instructionPC 2611 = 3323 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3777 : runtimeArtifact.instructionPC 2647 = 3370 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3778 : runtimeArtifact.instructionPC 2787 = 3562 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3779 : runtimeArtifact.instructionPC 2788 = 3565 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3787 : runtimeArtifact.instructionPC 2789 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3788 : runtimeArtifact.instructionPC 2789 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3789 : runtimeArtifact.instructionPC 2789 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3790 : runtimeArtifact.instructionPC 2789 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3791 : runtimeArtifact.instructionPC 2789 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3792 : runtimeArtifact.instructionPC 2789 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3793 : runtimeArtifact.instructionPC 2790 = 3567 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3794 : runtimeArtifact.instructionPC 2791 = 3570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3795 : runtimeArtifact.instructionPC 2792 = 3573 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3796 : runtimeArtifact.instructionPC 2793 = 3574 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3797 : runtimeArtifact.instructionPC 2794 = 3575 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3798 : runtimeArtifact.instructionPC 2794 = 3575 := fixedPC3797

@[simp] theorem fixedPC3799 : runtimeArtifact.instructionPC 2794 = 3575 := fixedPC3797

@[simp] theorem fixedPC3800 : runtimeArtifact.instructionPC 2795 = 3576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3801 : runtimeArtifact.instructionPC 2796 = 3577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3802 : runtimeArtifact.instructionPC 2797 = 3578 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3803 : runtimeArtifact.instructionPC 2798 = 3581 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3804 : runtimeArtifact.instructionPC 2799 = 3584 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : runtimeArtifact.instructionPC 2648 = 3371 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3115 : runtimeArtifact.instructionPC 2649 = 3372 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3116 : runtimeArtifact.instructionPC 2650 = 3373 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3117 : runtimeArtifact.instructionPC 2651 = 3376 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3118 : runtimeArtifact.instructionPC 2652 = 3379 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3119 : runtimeArtifact.instructionPC 2653 = 3382 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : runtimeArtifact.instructionPC 2617 = 3332 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4605 = true := by
  have h : runtimeArtifact.instructionPC 3597 = 4605 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 3597 (by rfl)

@[simp] theorem fixedPC3805 : runtimeArtifact.instructionPC 2654 = 3383 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3806 : runtimeArtifact.instructionPC 2655 = 3385 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3807 : runtimeArtifact.instructionPC 2656 = 3386 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3808 : runtimeArtifact.instructionPC 2657 = 3389 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPCs8 : runtimeArtifact.instructionPC 2658 = 3390 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3809 : runtimeArtifact.instructionPC 2658 = 3390 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3810 : runtimeArtifact.instructionPC 2659 = 3393 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3811 : runtimeArtifact.instructionPC 2660 = 3394 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3812 : runtimeArtifact.instructionPC 2661 = 3396 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3813 : runtimeArtifact.instructionPC 2662 = 3397 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3814 : runtimeArtifact.instructionPC 2663 = 3398 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3815 : runtimeArtifact.instructionPC 2664 = 3399 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3816 : runtimeArtifact.instructionPC 2664 = 3399 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3817 : runtimeArtifact.instructionPC 2665 = 3400 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3818 : runtimeArtifact.instructionPC 2666 = 3403 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3819 : runtimeArtifact.instructionPC 2667 = 3404 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3820 : runtimeArtifact.instructionPC 2668 = 3405 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3821 : runtimeArtifact.instructionPC 2669 = 3406 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3822 : runtimeArtifact.instructionPC 2670 = 3408 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3823 : runtimeArtifact.instructionPC 2671 = 3409 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3824 : runtimeArtifact.instructionPC 2672 = 3410 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3825 : runtimeArtifact.instructionPC 2673 = 3411 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3826 : runtimeArtifact.instructionPC 2674 = 3414 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3827 : runtimeArtifact.instructionPC 2675 = 3415 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3828 : runtimeArtifact.instructionPC 2676 = 3416 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3829 : runtimeArtifact.instructionPC 2677 = 3417 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3830 : runtimeArtifact.instructionPC 2678 = 3418 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3831 : runtimeArtifact.instructionPC 2679 = 3421 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3832 : runtimeArtifact.instructionPC 2680 = 3422 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3833 : runtimeArtifact.instructionPC 2681 = 3423 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3834 : runtimeArtifact.instructionPC 2681 = 3423 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3835 : runtimeArtifact.instructionPC 2682 = 3424 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3836 : runtimeArtifact.instructionPC 2683 = 3425 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3837 : runtimeArtifact.instructionPC 2684 = 3426 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3838 : runtimeArtifact.instructionPC 2685 = 3427 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3839 : runtimeArtifact.instructionPC 2686 = 3429 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3840 : runtimeArtifact.instructionPC 2687 = 3430 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3841 : runtimeArtifact.instructionPC 2688 = 3431 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3842 : runtimeArtifact.instructionPC 2689 = 3432 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3843 : runtimeArtifact.instructionPC 2690 = 3435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3844 : runtimeArtifact.instructionPC 2691 = 3436 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3845 : runtimeArtifact.instructionPC 2692 = 3437 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3846 : runtimeArtifact.instructionPC 2693 = 3438 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3847 : runtimeArtifact.instructionPC 2694 = 3439 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3848 : runtimeArtifact.instructionPC 2695 = 3442 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3849 : runtimeArtifact.instructionPC 2696 = 3443 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3850 : runtimeArtifact.instructionPC 2697 = 3444 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3851 : runtimeArtifact.instructionPC 2698 = 3445 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3852 : runtimeArtifact.instructionPC 2698 = 3445 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3853 : runtimeArtifact.instructionPC 2699 = 3446 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3854 : runtimeArtifact.instructionPC 2700 = 3447 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3855 : runtimeArtifact.instructionPC 2701 = 3448 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3856 : runtimeArtifact.instructionPC 2702 = 3450 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3857 : runtimeArtifact.instructionPC 2703 = 3451 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3858 : runtimeArtifact.instructionPC 2704 = 3452 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3859 : runtimeArtifact.instructionPC 2705 = 3453 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3860 : runtimeArtifact.instructionPC 2706 = 3456 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3861 : runtimeArtifact.instructionPC 2707 = 3457 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3862 : runtimeArtifact.instructionPC 2708 = 3458 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3863 : runtimeArtifact.instructionPC 2709 = 3459 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3864 : runtimeArtifact.instructionPC 2710 = 3460 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3865 : runtimeArtifact.instructionPC 2711 = 3463 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3866 : runtimeArtifact.instructionPC 2712 = 3464 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3867 : runtimeArtifact.instructionPC 2713 = 3465 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3868 : runtimeArtifact.instructionPC 2714 = 3466 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3869 : runtimeArtifact.instructionPC 2715 = 3467 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3871 : runtimeArtifact.instructionPC 2715 = 3467 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3872 : runtimeArtifact.instructionPC 2716 = 3468 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3873 : runtimeArtifact.instructionPC 2717 = 3469 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3874 : runtimeArtifact.instructionPC 2718 = 3471 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3875 : runtimeArtifact.instructionPC 2719 = 3472 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3876 : runtimeArtifact.instructionPC 2720 = 3473 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3877 : runtimeArtifact.instructionPC 2721 = 3474 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3878 : runtimeArtifact.instructionPC 2722 = 3477 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3879 : runtimeArtifact.instructionPC 2723 = 3478 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3880 : runtimeArtifact.instructionPC 2724 = 3479 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3881 : runtimeArtifact.instructionPC 2725 = 3480 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3882 : runtimeArtifact.instructionPC 2726 = 3481 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3883 : runtimeArtifact.instructionPC 2727 = 3484 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3884 : runtimeArtifact.instructionPC 2728 = 3485 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3885 : runtimeArtifact.instructionPC 2729 = 3486 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3886 : runtimeArtifact.instructionPC 2730 = 3487 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3887 : runtimeArtifact.instructionPC 2731 = 3488 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3888 : runtimeArtifact.instructionPC 2732 = 3489 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3889 : runtimeArtifact.instructionPC 2732 = 3489 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3489 = true := by
  have h : runtimeArtifact.instructionPC 2732 = 3489 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2732 (by rfl)

@[simp] theorem fixedPC3890 : runtimeArtifact.instructionPC 2733 = 3490 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3891 : runtimeArtifact.instructionPC 2734 = 3491 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3892 : runtimeArtifact.instructionPC 2735 = 3493 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3893 : runtimeArtifact.instructionPC 2736 = 3494 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3894 : runtimeArtifact.instructionPC 2737 = 3495 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3895 : runtimeArtifact.instructionPC 2738 = 3496 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3896 : runtimeArtifact.instructionPC 2739 = 3499 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3897 : runtimeArtifact.instructionPC 2740 = 3500 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3898 : runtimeArtifact.instructionPC 2741 = 3501 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3899 : runtimeArtifact.instructionPC 2742 = 3502 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3900 : runtimeArtifact.instructionPC 2743 = 3503 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3901 : runtimeArtifact.instructionPC 2744 = 3506 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3902 : runtimeArtifact.instructionPC 2745 = 3507 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3903 : runtimeArtifact.instructionPC 2746 = 3508 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3904 : runtimeArtifact.instructionPC 2747 = 3509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3905 : runtimeArtifact.instructionPC 2748 = 3510 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3906 : runtimeArtifact.instructionPC 2749 = 3511 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3907 : runtimeArtifact.instructionPC 2750 = 3512 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3908 : runtimeArtifact.instructionPC 2750 = 3512 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3909 : runtimeArtifact.instructionPC 2751 = 3514 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3910 : runtimeArtifact.instructionPC 2752 = 3515 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3911 : runtimeArtifact.instructionPC 2753 = 3516 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3912 : runtimeArtifact.instructionPC 2754 = 3517 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3913 : runtimeArtifact.instructionPC 2755 = 3520 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3914 : runtimeArtifact.instructionPC 2756 = 3521 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3915 : runtimeArtifact.instructionPC 2757 = 3522 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3916 : runtimeArtifact.instructionPC 2758 = 3523 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3917 : runtimeArtifact.instructionPC 2759 = 3524 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3918 : runtimeArtifact.instructionPC 2760 = 3527 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3919 : runtimeArtifact.instructionPC 2761 = 3528 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3920 : runtimeArtifact.instructionPC 2762 = 3529 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3921 : runtimeArtifact.instructionPC 2763 = 3530 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3922 : runtimeArtifact.instructionPC 2764 = 3531 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3923 : runtimeArtifact.instructionPC 2765 = 3532 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3924 : runtimeArtifact.instructionPC 2766 = 3533 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3925 : runtimeArtifact.instructionPC 2767 = 3534 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3926 : runtimeArtifact.instructionPC 2767 = 3534 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3927 : runtimeArtifact.instructionPC 2768 = 3535 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3928 : runtimeArtifact.instructionPC 2769 = 3536 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3929 : runtimeArtifact.instructionPC 2770 = 3537 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3930 : runtimeArtifact.instructionPC 2771 = 3540 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3931 : runtimeArtifact.instructionPC 2772 = 3541 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3932 : runtimeArtifact.instructionPC 2773 = 3542 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3933 : runtimeArtifact.instructionPC 2774 = 3543 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3934 : runtimeArtifact.instructionPC 2775 = 3544 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3935 : runtimeArtifact.instructionPC 2776 = 3547 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3936 : runtimeArtifact.instructionPC 2777 = 3548 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3937 : runtimeArtifact.instructionPC 2778 = 3549 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3938 : runtimeArtifact.instructionPC 2779 = 3550 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3939 : runtimeArtifact.instructionPC 2780 = 3551 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3940 : runtimeArtifact.instructionPC 2781 = 3552 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3941 : runtimeArtifact.instructionPC 2782 = 3553 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3942 : runtimeArtifact.instructionPC 2783 = 3556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3943 : runtimeArtifact.instructionPC 2784 = 3557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3944 : runtimeArtifact.instructionPC 2784 = 3557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3945 : runtimeArtifact.instructionPC 2785 = 3558 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3946 : runtimeArtifact.instructionPC 2786 = 3561 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3947 : runtimeArtifact.instructionPC 2787 = 3562 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3948 : runtimeArtifact.instructionPC 2788 = 3565 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3949 : runtimeArtifact.instructionPC 2793 = 3574 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3950 : runtimeArtifact.instructionPC 2793 = 3574 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : runtimeArtifact.instructionPC 2794 = 3575 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3952 : runtimeArtifact.instructionPC 2795 = 3576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3953 : runtimeArtifact.instructionPC 2796 = 3577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3954 : runtimeArtifact.instructionPC 2797 = 3578 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3955 : runtimeArtifact.instructionPC 2798 = 3581 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3956 : runtimeArtifact.instructionPC 2799 = 3584 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3957 : runtimeArtifact.instructionPC 2800 = 3585 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4605 = true := by
  have h : runtimeArtifact.instructionPC 3597 = 4605 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 3597 (by rfl)

@[simp] theorem fixedPC4000 : runtimeArtifact.instructionPC 2617 = 3332 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4001 : runtimeArtifact.instructionPC 2617 = 3332 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4002 : runtimeArtifact.instructionPC 2636 = 3355 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4003 : runtimeArtifact.instructionPC 3597 = 4605 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4004 : runtimeArtifact.instructionPC 3598 = 4606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4005 : runtimeArtifact.instructionPC 3599 = 4609 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4006 : runtimeArtifact.instructionPC 3600 = 4610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4007 : runtimeArtifact.instructionPC 3601 = 4612 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4008 : runtimeArtifact.instructionPC 3602 = 4613 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4009 : runtimeArtifact.instructionPC 3603 = 4614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4010 : runtimeArtifact.instructionPC 3604 = 4615 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4011 : runtimeArtifact.instructionPC 3605 = 4616 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4012 : runtimeArtifact.instructionPC 3606 = 4619 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2883 : runtimeArtifact.instructionPC 2595 = 3299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2884 : runtimeArtifact.instructionPC 2596 = 3300 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2885 : runtimeArtifact.instructionPC 2597 = 3301 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2886 : runtimeArtifact.instructionPC 2598 = 3302 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2888 : runtimeArtifact.instructionPC 2599 = 3303 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2889 : runtimeArtifact.instructionPC 2600 = 3304 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2890 : runtimeArtifact.instructionPC 2601 = 3305 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2891 : runtimeArtifact.instructionPC 2602 = 3308 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2892 : runtimeArtifact.instructionPC 2603 = 3309 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2893 : runtimeArtifact.instructionPC 2603 = 3309 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2894 : runtimeArtifact.instructionPC 2604 = 3312 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2895 : runtimeArtifact.instructionPC 2605 = 3313 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2896 : runtimeArtifact.instructionPC 2617 = 3332 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2930 : runtimeArtifact.instructionPC 2617 = 3332 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2931 : runtimeArtifact.instructionPC 2617 = 3332 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2932 : runtimeArtifact.instructionPC 2617 = 3332 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2933 : runtimeArtifact.instructionPC 2636 = 3355 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2934 : runtimeArtifact.instructionPC 3597 = 4605 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2935 : runtimeArtifact.instructionPC 3598 = 4606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2936 : runtimeArtifact.instructionPC 3599 = 4609 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2937 : runtimeArtifact.instructionPC 3600 = 4610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2938 : runtimeArtifact.instructionPC 3601 = 4612 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2939 : runtimeArtifact.instructionPC 3602 = 4613 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2940 : runtimeArtifact.instructionPC 3603 = 4614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2941 : runtimeArtifact.instructionPC 3604 = 4615 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2942 : runtimeArtifact.instructionPC 3605 = 4616 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2943 : runtimeArtifact.instructionPC 3606 = 4619 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3921 : runtimeArtifact.instructionPC 2789 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3922 : runtimeArtifact.instructionPC 2789 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3923 : runtimeArtifact.instructionPC 2789 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3924 : runtimeArtifact.instructionPC 2789 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3925 : runtimeArtifact.instructionPC 2789 = 3566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3926 : runtimeArtifact.instructionPC 2790 = 3567 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3927 : runtimeArtifact.instructionPC 2791 = 3570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3928 : runtimeArtifact.instructionPC 2792 = 3573 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

end CycleSubmission.Global.Fast
