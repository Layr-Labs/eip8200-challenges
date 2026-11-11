import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PrefixPC
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
open CycleSubmission.SharedStackArgs

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
  [pushAt 2664 2 2688,
   opAt 2665 .MLOAD,
   pushAt 2666 1 128,
   opAt 2667 .EQ,
   pushAt 2668 2 3453,
   opAt 2669 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2664 2 2688,
   opAt 2665 .MLOAD,
   pushAt 2666 1 128,
   opAt 2667 .EQ,
   pushAt 2668 2 3453,
   opAt 2669 .JUMPI,
   opAt 2632 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2670 .JUMPDEST,
   pushAt 2671 2 2336,
   opAt 2672 .MLOAD,
   pushAt 2673 1 224,
   opAt 2674 .MLOAD,
   opAt 2675 (.Dup dA0),
   opAt 2676 (.Dup dA2),
   opAt 2677 .SUB,
   pushAt 2678 2 2016,
   opAt 2679 .MSTORE,
   opAt 2680 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2681 (.Dup dA0),
   pushAt 2682 1 192,
   opAt 2683 .MLOAD,
   opAt 2684 .ADD,
   opAt 2685 (.Dup dA0),
   pushAt 2686 2 2304,
   opAt 2687 .MLOAD,
   opAt 2688 (.Dup dA1),
   opAt 2689 (.Dup dA1),
   opAt 2690 .SUB,
   pushAt 2691 2 1984,
   opAt 2692 .MSTORE,
   opAt 2693 .LT,
   opAt 2694 (.Swap sA1),
   opAt 2695 .GT,
   opAt 2696 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2697 (.Dup dA0),
   pushAt 2698 1 160,
   opAt 2699 .MLOAD,
   opAt 2700 .ADD,
   opAt 2701 (.Dup dA0),
   pushAt 2702 2 2272,
   opAt 2703 .MLOAD,
   opAt 2704 (.Dup dA1),
   opAt 2705 (.Dup dA1),
   opAt 2706 .SUB,
   pushAt 2707 2 1952,
   opAt 2708 .MSTORE,
   opAt 2709 .LT,
   opAt 2710 (.Swap sA1),
   opAt 2711 .GT,
   opAt 2712 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2713 (.Dup dA0),
   pushAt 2714 1 128,
   opAt 2715 .MLOAD,
   opAt 2716 .ADD,
   opAt 2717 (.Dup dA0),
   pushAt 2718 2 2240,
   opAt 2719 .MLOAD,
   opAt 2720 (.Dup dA1),
   opAt 2721 (.Dup dA1),
   opAt 2722 .SUB,
   pushAt 2723 2 1920,
   opAt 2724 .MSTORE,
   opAt 2725 .LT,
   opAt 2726 (.Swap sA1),
   opAt 2727 .GT,
   opAt 2728 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2729 (.Dup dA0),
   pushAt 2730 1 96,
   opAt 2731 .MLOAD,
   opAt 2732 .ADD,
   opAt 2733 (.Dup dA0),
   pushAt 2734 2 2208,
   opAt 2735 .MLOAD,
   opAt 2736 (.Dup dA1),
   opAt 2737 (.Dup dA1),
   opAt 2738 .SUB,
   pushAt 2739 2 1888,
   opAt 2740 .MSTORE,
   opAt 2741 .LT,
   opAt 2742 (.Swap sA1),
   opAt 2743 .GT,
   opAt 2744 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2745 .JUMPDEST,
   opAt 2746 (.Dup dA0),
   pushAt 2747 1 64,
   opAt 2748 .MLOAD,
   opAt 2749 .ADD,
   opAt 2750 (.Dup dA0),
   pushAt 2751 2 2176,
   opAt 2752 .MLOAD,
   opAt 2753 (.Dup dA1),
   opAt 2754 (.Dup dA1),
   opAt 2755 .SUB,
   pushAt 2756 2 1856,
   opAt 2757 .MSTORE,
   opAt 2758 .LT,
   opAt 2759 (.Swap sA1),
   opAt 2760 .GT,
   opAt 2761 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2762 (.Dup dA0),
   pushAt 2763 1 32,
   opAt 2764 .MLOAD,
   opAt 2765 .ADD,
   opAt 2766 (.Dup dA0),
   pushAt 2767 2 2144,
   opAt 2768 .MLOAD,
   opAt 2769 (.Dup dA1),
   opAt 2770 (.Dup dA1),
   opAt 2771 .SUB,
   pushAt 2772 2 1824,
   opAt 2773 .MSTORE,
   opAt 2774 .LT,
   opAt 2775 (.Swap sA1),
   opAt 2776 .GT,
   opAt 2777 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2778 (.Dup dA0),
   pushAt 2779 0 0,
   opAt 2780 .MLOAD,
   opAt 2781 .ADD,
   opAt 2782 (.Dup dA0),
   pushAt 2783 2 2112,
   opAt 2784 .MLOAD,
   opAt 2785 (.Dup dA1),
   opAt 2786 (.Dup dA1),
   opAt 2787 .SUB,
   pushAt 2788 2 1792,
   opAt 2789 .MSTORE,
   opAt 2790 .LT,
   opAt 2791 (.Swap sA1),
   opAt 2792 .GT,
   opAt 2793 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2794 .ISZERO,
   pushAt 2795 2 2080,
   opAt 2796 .MLOAD,
   opAt 2797 .OR,
   pushAt 2798 2 3699,
   opAt 2799 .JUMPI,
   opAt 2809 .JUMPDEST,
   pushAt 2810 2 1792,
   pushAt 2811 2 2688,
   opAt 2812 .MLOAD,
   opAt 2813 (.Swap sA1),
   opAt 2814 .MCOPY,
   opAt 2815 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2794 .ISZERO,
   pushAt 2795 2 2080,
   opAt 2796 .MLOAD,
   opAt 2797 .OR,
   pushAt 2798 2 3699,
   opAt 2799 .JUMPI,
   pushAt 2800 2 3688,
   opAt 2801 .JUMP,
   opAt 2802 .JUMPDEST,
   pushAt 2803 2 2112,
   pushAt 2804 2 2688,
   opAt 2805 .MLOAD,
   opAt 2806 (.Swap sA1),
   opAt 2807 .MCOPY,
   opAt 2808 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2633 2 2208,
   opAt 2634 .MLOAD,
   pushAt 2635 1 96,
   opAt 2636 .MLOAD,
   opAt 2637 (.Dup dA0),
   opAt 2638 (.Dup dA2),
   opAt 2639 .SUB,
   pushAt 2640 2 1888,
   opAt 2641 .MSTORE,
   opAt 2642 .GT,
   pushAt 2643 2 3611,
   opAt 2644 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2745 .JUMPDEST,
   opAt 2746 (.Dup dA0),
   pushAt 2747 1 64,
   opAt 2748 .MLOAD,
   opAt 2749 .ADD,
   opAt 2750 (.Dup dA0),
   pushAt 2751 2 2176,
   opAt 2752 .MLOAD,
   opAt 2753 (.Dup dA1),
   opAt 2754 (.Dup dA1),
   opAt 2755 .SUB,
   pushAt 2756 2 1856,
   opAt 2757 .MSTORE,
   opAt 2758 .LT,
   opAt 2759 (.Swap sA1),
   opAt 2760 .GT,
   opAt 2761 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2762 (.Dup dA0),
   pushAt 2763 1 32,
   opAt 2764 .MLOAD,
   opAt 2765 .ADD,
   opAt 2766 (.Dup dA0),
   pushAt 2767 2 2144,
   opAt 2768 .MLOAD,
   opAt 2769 (.Dup dA1),
   opAt 2770 (.Dup dA1),
   opAt 2771 .SUB,
   pushAt 2772 2 1824,
   opAt 2773 .MSTORE,
   opAt 2774 .LT,
   opAt 2775 (.Swap sA1),
   opAt 2776 .GT,
   opAt 2777 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2778 (.Dup dA0),
   pushAt 2779 0 0,
   opAt 2780 .MLOAD,
   opAt 2781 .ADD,
   opAt 2782 (.Dup dA0),
   pushAt 2783 2 2112,
   opAt 2784 .MLOAD,
   opAt 2785 (.Dup dA1),
   opAt 2786 (.Dup dA1),
   opAt 2787 .SUB,
   pushAt 2788 2 1792,
   opAt 2789 .MSTORE,
   opAt 2790 .LT,
   opAt 2791 (.Swap sA1),
   opAt 2792 .GT,
   opAt 2793 .OR]

@[simp] theorem cycleAnchor : CycleSubmission.Artifact.artifact.instructionPC 2623 = 3438 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3777 : CycleSubmission.Artifact.artifact.instructionPC 2659 = 3491 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3778 : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3684 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3779 : CycleSubmission.Artifact.artifact.instructionPC 2801 = 3687 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3787 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3688 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3788 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3688 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3789 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3688 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3790 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3688 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3791 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3688 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3792 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3688 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3793 : CycleSubmission.Artifact.artifact.instructionPC 2803 = 3689 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3794 : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3692 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3795 : CycleSubmission.Artifact.artifact.instructionPC 2805 = 3695 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3796 : CycleSubmission.Artifact.artifact.instructionPC 2806 = 3696 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3797 : CycleSubmission.Artifact.artifact.instructionPC 2807 = 3697 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3798 : CycleSubmission.Artifact.artifact.instructionPC 2807 = 3697 := fixedPC3797

@[simp] theorem fixedPC3799 : CycleSubmission.Artifact.artifact.instructionPC 2807 = 3697 := fixedPC3797

@[simp] theorem fixedPC3800 : CycleSubmission.Artifact.artifact.instructionPC 2808 = 3698 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3801 : CycleSubmission.Artifact.artifact.instructionPC 2809 = 3699 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3802 : CycleSubmission.Artifact.artifact.instructionPC 2810 = 3700 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3803 : CycleSubmission.Artifact.artifact.instructionPC 2811 = 3703 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3804 : CycleSubmission.Artifact.artifact.instructionPC 2812 = 3706 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : CycleSubmission.Artifact.artifact.instructionPC 2660 = 3492 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3115 : CycleSubmission.Artifact.artifact.instructionPC 2661 = 3493 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3116 : CycleSubmission.Artifact.artifact.instructionPC 2662 = 3494 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3117 : CycleSubmission.Artifact.artifact.instructionPC 2663 = 3497 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3118 : CycleSubmission.Artifact.artifact.instructionPC 2664 = 3500 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3119 : CycleSubmission.Artifact.artifact.instructionPC 2665 = 3503 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : CycleSubmission.Artifact.artifact.instructionPC 2629 = 3448 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3453 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2632 = 3453 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2632 (by rfl)

@[simp] theorem fixedPC3805 : CycleSubmission.Artifact.artifact.instructionPC 2666 = 3504 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3806 : CycleSubmission.Artifact.artifact.instructionPC 2667 = 3506 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3807 : CycleSubmission.Artifact.artifact.instructionPC 2668 = 3507 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3808 : CycleSubmission.Artifact.artifact.instructionPC 2669 = 3510 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPCs8 : CycleSubmission.Artifact.artifact.instructionPC 2670 = 3511 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3809 : CycleSubmission.Artifact.artifact.instructionPC 2671 = 3512 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3810 : CycleSubmission.Artifact.artifact.instructionPC 2672 = 3515 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3811 : CycleSubmission.Artifact.artifact.instructionPC 2673 = 3516 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3812 : CycleSubmission.Artifact.artifact.instructionPC 2674 = 3518 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3813 : CycleSubmission.Artifact.artifact.instructionPC 2675 = 3519 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3814 : CycleSubmission.Artifact.artifact.instructionPC 2676 = 3520 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3815 : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3521 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3816 : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3521 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3817 : CycleSubmission.Artifact.artifact.instructionPC 2678 = 3522 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3818 : CycleSubmission.Artifact.artifact.instructionPC 2679 = 3525 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3819 : CycleSubmission.Artifact.artifact.instructionPC 2680 = 3526 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3820 : CycleSubmission.Artifact.artifact.instructionPC 2681 = 3527 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3821 : CycleSubmission.Artifact.artifact.instructionPC 2682 = 3528 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3822 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3530 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3823 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3531 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3824 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3532 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3825 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3533 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3826 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3536 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3827 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3537 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3828 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3538 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3829 : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3539 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3830 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3540 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3831 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3543 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3832 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3544 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3833 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3545 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3834 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3545 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3835 : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3546 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3836 : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3547 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3837 : CycleSubmission.Artifact.artifact.instructionPC 2697 = 3548 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3838 : CycleSubmission.Artifact.artifact.instructionPC 2698 = 3549 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3839 : CycleSubmission.Artifact.artifact.instructionPC 2699 = 3551 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3840 : CycleSubmission.Artifact.artifact.instructionPC 2700 = 3552 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3841 : CycleSubmission.Artifact.artifact.instructionPC 2701 = 3553 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3842 : CycleSubmission.Artifact.artifact.instructionPC 2702 = 3554 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3843 : CycleSubmission.Artifact.artifact.instructionPC 2703 = 3557 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3844 : CycleSubmission.Artifact.artifact.instructionPC 2704 = 3558 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3845 : CycleSubmission.Artifact.artifact.instructionPC 2705 = 3559 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3846 : CycleSubmission.Artifact.artifact.instructionPC 2706 = 3560 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3847 : CycleSubmission.Artifact.artifact.instructionPC 2707 = 3561 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3848 : CycleSubmission.Artifact.artifact.instructionPC 2708 = 3564 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3849 : CycleSubmission.Artifact.artifact.instructionPC 2709 = 3565 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3850 : CycleSubmission.Artifact.artifact.instructionPC 2710 = 3566 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3851 : CycleSubmission.Artifact.artifact.instructionPC 2711 = 3567 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3852 : CycleSubmission.Artifact.artifact.instructionPC 2711 = 3567 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3853 : CycleSubmission.Artifact.artifact.instructionPC 2712 = 3568 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3854 : CycleSubmission.Artifact.artifact.instructionPC 2713 = 3569 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3855 : CycleSubmission.Artifact.artifact.instructionPC 2714 = 3570 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3856 : CycleSubmission.Artifact.artifact.instructionPC 2715 = 3572 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3857 : CycleSubmission.Artifact.artifact.instructionPC 2716 = 3573 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3858 : CycleSubmission.Artifact.artifact.instructionPC 2717 = 3574 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3859 : CycleSubmission.Artifact.artifact.instructionPC 2718 = 3575 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3860 : CycleSubmission.Artifact.artifact.instructionPC 2719 = 3578 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3861 : CycleSubmission.Artifact.artifact.instructionPC 2720 = 3579 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3862 : CycleSubmission.Artifact.artifact.instructionPC 2721 = 3580 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3863 : CycleSubmission.Artifact.artifact.instructionPC 2722 = 3581 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3864 : CycleSubmission.Artifact.artifact.instructionPC 2723 = 3582 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3865 : CycleSubmission.Artifact.artifact.instructionPC 2724 = 3585 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3866 : CycleSubmission.Artifact.artifact.instructionPC 2725 = 3586 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3867 : CycleSubmission.Artifact.artifact.instructionPC 2726 = 3587 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3868 : CycleSubmission.Artifact.artifact.instructionPC 2727 = 3588 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3869 : CycleSubmission.Artifact.artifact.instructionPC 2728 = 3589 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3871 : CycleSubmission.Artifact.artifact.instructionPC 2728 = 3589 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3872 : CycleSubmission.Artifact.artifact.instructionPC 2729 = 3590 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3873 : CycleSubmission.Artifact.artifact.instructionPC 2730 = 3591 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3874 : CycleSubmission.Artifact.artifact.instructionPC 2731 = 3593 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3875 : CycleSubmission.Artifact.artifact.instructionPC 2732 = 3594 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3876 : CycleSubmission.Artifact.artifact.instructionPC 2733 = 3595 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3877 : CycleSubmission.Artifact.artifact.instructionPC 2734 = 3596 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3878 : CycleSubmission.Artifact.artifact.instructionPC 2735 = 3599 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3879 : CycleSubmission.Artifact.artifact.instructionPC 2736 = 3600 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3880 : CycleSubmission.Artifact.artifact.instructionPC 2737 = 3601 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3881 : CycleSubmission.Artifact.artifact.instructionPC 2738 = 3602 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3882 : CycleSubmission.Artifact.artifact.instructionPC 2739 = 3603 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3883 : CycleSubmission.Artifact.artifact.instructionPC 2740 = 3606 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3884 : CycleSubmission.Artifact.artifact.instructionPC 2741 = 3607 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3885 : CycleSubmission.Artifact.artifact.instructionPC 2742 = 3608 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3886 : CycleSubmission.Artifact.artifact.instructionPC 2743 = 3609 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3887 : CycleSubmission.Artifact.artifact.instructionPC 2744 = 3610 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3888 : CycleSubmission.Artifact.artifact.instructionPC 2745 = 3611 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3889 : CycleSubmission.Artifact.artifact.instructionPC 2745 = 3611 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3611 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2745 = 3611 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2745 (by rfl)

@[simp] theorem fixedPC3890 : CycleSubmission.Artifact.artifact.instructionPC 2746 = 3612 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3891 : CycleSubmission.Artifact.artifact.instructionPC 2747 = 3613 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3892 : CycleSubmission.Artifact.artifact.instructionPC 2748 = 3615 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3893 : CycleSubmission.Artifact.artifact.instructionPC 2749 = 3616 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3894 : CycleSubmission.Artifact.artifact.instructionPC 2750 = 3617 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3895 : CycleSubmission.Artifact.artifact.instructionPC 2751 = 3618 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3896 : CycleSubmission.Artifact.artifact.instructionPC 2752 = 3621 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3897 : CycleSubmission.Artifact.artifact.instructionPC 2753 = 3622 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3898 : CycleSubmission.Artifact.artifact.instructionPC 2754 = 3623 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3899 : CycleSubmission.Artifact.artifact.instructionPC 2755 = 3624 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3900 : CycleSubmission.Artifact.artifact.instructionPC 2756 = 3625 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3901 : CycleSubmission.Artifact.artifact.instructionPC 2757 = 3628 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3902 : CycleSubmission.Artifact.artifact.instructionPC 2758 = 3629 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3903 : CycleSubmission.Artifact.artifact.instructionPC 2759 = 3630 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3904 : CycleSubmission.Artifact.artifact.instructionPC 2760 = 3631 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3905 : CycleSubmission.Artifact.artifact.instructionPC 2761 = 3632 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3906 : CycleSubmission.Artifact.artifact.instructionPC 2762 = 3633 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3907 : CycleSubmission.Artifact.artifact.instructionPC 2763 = 3634 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3908 : CycleSubmission.Artifact.artifact.instructionPC 2763 = 3634 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3909 : CycleSubmission.Artifact.artifact.instructionPC 2764 = 3636 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3910 : CycleSubmission.Artifact.artifact.instructionPC 2765 = 3637 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3911 : CycleSubmission.Artifact.artifact.instructionPC 2766 = 3638 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3912 : CycleSubmission.Artifact.artifact.instructionPC 2767 = 3639 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3913 : CycleSubmission.Artifact.artifact.instructionPC 2768 = 3642 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3914 : CycleSubmission.Artifact.artifact.instructionPC 2769 = 3643 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3915 : CycleSubmission.Artifact.artifact.instructionPC 2770 = 3644 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3916 : CycleSubmission.Artifact.artifact.instructionPC 2771 = 3645 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3917 : CycleSubmission.Artifact.artifact.instructionPC 2772 = 3646 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3918 : CycleSubmission.Artifact.artifact.instructionPC 2773 = 3649 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3919 : CycleSubmission.Artifact.artifact.instructionPC 2774 = 3650 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3920 : CycleSubmission.Artifact.artifact.instructionPC 2775 = 3651 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2776 = 3652 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2777 = 3653 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2778 = 3654 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2779 = 3655 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2780 = 3656 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2780 = 3656 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2781 = 3657 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2782 = 3658 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3929 : CycleSubmission.Artifact.artifact.instructionPC 2783 = 3659 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3930 : CycleSubmission.Artifact.artifact.instructionPC 2784 = 3662 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3931 : CycleSubmission.Artifact.artifact.instructionPC 2785 = 3663 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3932 : CycleSubmission.Artifact.artifact.instructionPC 2786 = 3664 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3933 : CycleSubmission.Artifact.artifact.instructionPC 2787 = 3665 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3934 : CycleSubmission.Artifact.artifact.instructionPC 2788 = 3666 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3935 : CycleSubmission.Artifact.artifact.instructionPC 2789 = 3669 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3936 : CycleSubmission.Artifact.artifact.instructionPC 2790 = 3670 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3937 : CycleSubmission.Artifact.artifact.instructionPC 2791 = 3671 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3938 : CycleSubmission.Artifact.artifact.instructionPC 2792 = 3672 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3939 : CycleSubmission.Artifact.artifact.instructionPC 2793 = 3673 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3940 : CycleSubmission.Artifact.artifact.instructionPC 2794 = 3674 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3941 : CycleSubmission.Artifact.artifact.instructionPC 2795 = 3675 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3942 : CycleSubmission.Artifact.artifact.instructionPC 2796 = 3678 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3943 : CycleSubmission.Artifact.artifact.instructionPC 2797 = 3679 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3944 : CycleSubmission.Artifact.artifact.instructionPC 2797 = 3679 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3945 : CycleSubmission.Artifact.artifact.instructionPC 2798 = 3680 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3946 : CycleSubmission.Artifact.artifact.instructionPC 2799 = 3683 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3947 : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3684 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3948 : CycleSubmission.Artifact.artifact.instructionPC 2801 = 3687 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3949 : CycleSubmission.Artifact.artifact.instructionPC 2806 = 3696 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3950 : CycleSubmission.Artifact.artifact.instructionPC 2806 = 3696 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : CycleSubmission.Artifact.artifact.instructionPC 2807 = 3697 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3952 : CycleSubmission.Artifact.artifact.instructionPC 2808 = 3698 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3953 : CycleSubmission.Artifact.artifact.instructionPC 2809 = 3699 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3954 : CycleSubmission.Artifact.artifact.instructionPC 2810 = 3700 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3955 : CycleSubmission.Artifact.artifact.instructionPC 2811 = 3703 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3956 : CycleSubmission.Artifact.artifact.instructionPC 2812 = 3706 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3957 : CycleSubmission.Artifact.artifact.instructionPC 2813 = 3707 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3453 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2632 = 3453 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2632 (by rfl)

@[simp] theorem fixedPC4000 : CycleSubmission.Artifact.artifact.instructionPC 2629 = 3448 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4001 : CycleSubmission.Artifact.artifact.instructionPC 2630 = 3451 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4002 : CycleSubmission.Artifact.artifact.instructionPC 2631 = 3452 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4003 : CycleSubmission.Artifact.artifact.instructionPC 2632 = 3453 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4004 : CycleSubmission.Artifact.artifact.instructionPC 2633 = 3454 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4005 : CycleSubmission.Artifact.artifact.instructionPC 2634 = 3457 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4006 : CycleSubmission.Artifact.artifact.instructionPC 2635 = 3458 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4007 : CycleSubmission.Artifact.artifact.instructionPC 2636 = 3460 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4008 : CycleSubmission.Artifact.artifact.instructionPC 2637 = 3461 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4009 : CycleSubmission.Artifact.artifact.instructionPC 2638 = 3462 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4010 : CycleSubmission.Artifact.artifact.instructionPC 2639 = 3463 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4011 : CycleSubmission.Artifact.artifact.instructionPC 2640 = 3464 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4012 : CycleSubmission.Artifact.artifact.instructionPC 2641 = 3467 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2883 : CycleSubmission.Artifact.artifact.instructionPC 2607 = 3414 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : CycleSubmission.Artifact.artifact.instructionPC 2608 = 3415 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : CycleSubmission.Artifact.artifact.instructionPC 2609 = 3416 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : CycleSubmission.Artifact.artifact.instructionPC 2610 = 3417 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : CycleSubmission.Artifact.artifact.instructionPC 2611 = 3418 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : CycleSubmission.Artifact.artifact.instructionPC 2612 = 3419 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2890 : CycleSubmission.Artifact.artifact.instructionPC 2613 = 3420 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2891 : CycleSubmission.Artifact.artifact.instructionPC 2614 = 3423 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2892 : CycleSubmission.Artifact.artifact.instructionPC 2615 = 3424 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2893 : CycleSubmission.Artifact.artifact.instructionPC 2615 = 3424 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2894 : CycleSubmission.Artifact.artifact.instructionPC 2616 = 3427 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2895 : CycleSubmission.Artifact.artifact.instructionPC 2617 = 3428 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2896 : CycleSubmission.Artifact.artifact.instructionPC 2629 = 3448 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2930 : CycleSubmission.Artifact.artifact.instructionPC 2629 = 3448 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2931 : CycleSubmission.Artifact.artifact.instructionPC 2629 = 3448 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2932 : CycleSubmission.Artifact.artifact.instructionPC 2630 = 3451 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2933 : CycleSubmission.Artifact.artifact.instructionPC 2631 = 3452 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2934 : CycleSubmission.Artifact.artifact.instructionPC 2632 = 3453 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2935 : CycleSubmission.Artifact.artifact.instructionPC 2633 = 3454 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2936 : CycleSubmission.Artifact.artifact.instructionPC 2634 = 3457 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2937 : CycleSubmission.Artifact.artifact.instructionPC 2635 = 3458 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2938 : CycleSubmission.Artifact.artifact.instructionPC 2636 = 3460 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2939 : CycleSubmission.Artifact.artifact.instructionPC 2637 = 3461 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2940 : CycleSubmission.Artifact.artifact.instructionPC 2638 = 3462 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2941 : CycleSubmission.Artifact.artifact.instructionPC 2639 = 3463 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2942 : CycleSubmission.Artifact.artifact.instructionPC 2640 = 3464 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2943 : CycleSubmission.Artifact.artifact.instructionPC 2641 = 3467 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3688 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3688 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3688 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3688 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3688 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2803 = 3689 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3692 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2805 = 3695 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

end CycleSubmission.Global.Fast
