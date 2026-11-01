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
  [pushAt 2719 2 2688,
   opAt 2720 .MLOAD,
   pushAt 2721 1 128,
   opAt 2722 .EQ,
   pushAt 2723 2 3462,
   opAt 2724 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2719 2 2688,
   opAt 2720 .MLOAD,
   pushAt 2721 1 128,
   opAt 2722 .EQ,
   pushAt 2723 2 3462,
   opAt 2724 .JUMPI,
   opAt 2687 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2725 .JUMPDEST,
   pushAt 2726 2 2336,
   opAt 2727 .MLOAD,
   pushAt 2728 1 224,
   opAt 2729 .MLOAD,
   opAt 2730 (.Dup ⟨0, by decide⟩),
   opAt 2731 (.Dup ⟨2, by decide⟩),
   opAt 2732 .SUB,
   pushAt 2733 2 2016,
   opAt 2734 .MSTORE,
   opAt 2735 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2736 (.Dup ⟨0, by decide⟩),
   pushAt 2737 1 192,
   opAt 2738 .MLOAD,
   opAt 2739 .ADD,
   opAt 2740 (.Dup ⟨0, by decide⟩),
   pushAt 2741 2 2304,
   opAt 2742 .MLOAD,
   opAt 2743 (.Dup ⟨1, by decide⟩),
   opAt 2744 (.Dup ⟨1, by decide⟩),
   opAt 2745 .SUB,
   pushAt 2746 2 1984,
   opAt 2747 .MSTORE,
   opAt 2748 .LT,
   opAt 2749 (.Swap ⟨1, by decide⟩),
   opAt 2750 .GT,
   opAt 2751 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2752 (.Dup ⟨0, by decide⟩),
   pushAt 2753 1 160,
   opAt 2754 .MLOAD,
   opAt 2755 .ADD,
   opAt 2756 (.Dup ⟨0, by decide⟩),
   pushAt 2757 2 2272,
   opAt 2758 .MLOAD,
   opAt 2759 (.Dup ⟨1, by decide⟩),
   opAt 2760 (.Dup ⟨1, by decide⟩),
   opAt 2761 .SUB,
   pushAt 2762 2 1952,
   opAt 2763 .MSTORE,
   opAt 2764 .LT,
   opAt 2765 (.Swap ⟨1, by decide⟩),
   opAt 2766 .GT,
   opAt 2767 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2768 (.Dup ⟨0, by decide⟩),
   pushAt 2769 1 128,
   opAt 2770 .MLOAD,
   opAt 2771 .ADD,
   opAt 2772 (.Dup ⟨0, by decide⟩),
   pushAt 2773 2 2240,
   opAt 2774 .MLOAD,
   opAt 2775 (.Dup ⟨1, by decide⟩),
   opAt 2776 (.Dup ⟨1, by decide⟩),
   opAt 2777 .SUB,
   pushAt 2778 2 1920,
   opAt 2779 .MSTORE,
   opAt 2780 .LT,
   opAt 2781 (.Swap ⟨1, by decide⟩),
   opAt 2782 .GT,
   opAt 2783 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2784 (.Dup ⟨0, by decide⟩),
   pushAt 2785 1 96,
   opAt 2786 .MLOAD,
   opAt 2787 .ADD,
   opAt 2788 (.Dup ⟨0, by decide⟩),
   pushAt 2789 2 2208,
   opAt 2790 .MLOAD,
   opAt 2791 (.Dup ⟨1, by decide⟩),
   opAt 2792 (.Dup ⟨1, by decide⟩),
   opAt 2793 .SUB,
   pushAt 2794 2 1888,
   opAt 2795 .MSTORE,
   opAt 2796 .LT,
   opAt 2797 (.Swap ⟨1, by decide⟩),
   opAt 2798 .GT,
   opAt 2799 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2800 .JUMPDEST,
   opAt 2801 (.Dup ⟨0, by decide⟩),
   pushAt 2802 1 64,
   opAt 2803 .MLOAD,
   opAt 2804 .ADD,
   opAt 2805 (.Dup ⟨0, by decide⟩),
   pushAt 2806 2 2176,
   opAt 2807 .MLOAD,
   opAt 2808 (.Dup ⟨1, by decide⟩),
   opAt 2809 (.Dup ⟨1, by decide⟩),
   opAt 2810 .SUB,
   pushAt 2811 2 1856,
   opAt 2812 .MSTORE,
   opAt 2813 .LT,
   opAt 2814 (.Swap ⟨1, by decide⟩),
   opAt 2815 .GT,
   opAt 2816 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2817 (.Dup ⟨0, by decide⟩),
   pushAt 2818 1 32,
   opAt 2819 .MLOAD,
   opAt 2820 .ADD,
   opAt 2821 (.Dup ⟨0, by decide⟩),
   pushAt 2822 2 2144,
   opAt 2823 .MLOAD,
   opAt 2824 (.Dup ⟨1, by decide⟩),
   opAt 2825 (.Dup ⟨1, by decide⟩),
   opAt 2826 .SUB,
   pushAt 2827 2 1824,
   opAt 2828 .MSTORE,
   opAt 2829 .LT,
   opAt 2830 (.Swap ⟨1, by decide⟩),
   opAt 2831 .GT,
   opAt 2832 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2833 (.Dup ⟨0, by decide⟩),
   pushAt 2834 0 0,
   opAt 2835 .MLOAD,
   opAt 2836 .ADD,
   opAt 2837 (.Dup ⟨0, by decide⟩),
   pushAt 2838 2 2112,
   opAt 2839 .MLOAD,
   opAt 2840 (.Dup ⟨1, by decide⟩),
   opAt 2841 (.Dup ⟨1, by decide⟩),
   opAt 2842 .SUB,
   pushAt 2843 2 1792,
   opAt 2844 .MSTORE,
   opAt 2845 .LT,
   opAt 2846 (.Swap ⟨1, by decide⟩),
   opAt 2847 .GT,
   opAt 2848 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2849 .ISZERO,
   pushAt 2850 2 2080,
   opAt 2851 .MLOAD,
   opAt 2852 .OR,
   pushAt 2853 2 3717,
   opAt 2854 .JUMPI,
   opAt 2872 .JUMPDEST,
   pushAt 2873 2 1792,
   pushAt 2874 2 2688,
   opAt 2875 .MLOAD,
   opAt 2876 (.Swap ⟨1, by decide⟩),
   opAt 2877 .MCOPY,
   opAt 2878 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2849 .ISZERO,
   pushAt 2850 2 2080,
   opAt 2851 .MLOAD,
   opAt 2852 .OR,
   pushAt 2853 2 3717,
   opAt 2854 .JUMPI,
   pushAt 2855 2 3706,
   opAt 2856 .JUMP,
   opAt 2865 .JUMPDEST,
   pushAt 2866 2 2112,
   pushAt 2867 2 2688,
   opAt 2868 .MLOAD,
   opAt 2869 (.Swap ⟨1, by decide⟩),
   opAt 2870 .MCOPY,
   opAt 2871 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2688 2 2208,
   opAt 2689 .MLOAD,
   pushAt 2690 1 96,
   opAt 2691 .MLOAD,
   opAt 2692 (.Dup ⟨0, by decide⟩),
   opAt 2693 (.Dup ⟨2, by decide⟩),
   opAt 2694 .SUB,
   pushAt 2695 2 1888,
   opAt 2696 .MSTORE,
   opAt 2697 .GT,
   pushAt 2698 2 3620,
   opAt 2699 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2800 .JUMPDEST,
   opAt 2801 (.Dup ⟨0, by decide⟩),
   pushAt 2802 1 64,
   opAt 2803 .MLOAD,
   opAt 2804 .ADD,
   opAt 2805 (.Dup ⟨0, by decide⟩),
   pushAt 2806 2 2176,
   opAt 2807 .MLOAD,
   opAt 2808 (.Dup ⟨1, by decide⟩),
   opAt 2809 (.Dup ⟨1, by decide⟩),
   opAt 2810 .SUB,
   pushAt 2811 2 1856,
   opAt 2812 .MSTORE,
   opAt 2813 .LT,
   opAt 2814 (.Swap ⟨1, by decide⟩),
   opAt 2815 .GT,
   opAt 2816 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2817 (.Dup ⟨0, by decide⟩),
   pushAt 2818 1 32,
   opAt 2819 .MLOAD,
   opAt 2820 .ADD,
   opAt 2821 (.Dup ⟨0, by decide⟩),
   pushAt 2822 2 2144,
   opAt 2823 .MLOAD,
   opAt 2824 (.Dup ⟨1, by decide⟩),
   opAt 2825 (.Dup ⟨1, by decide⟩),
   opAt 2826 .SUB,
   pushAt 2827 2 1824,
   opAt 2828 .MSTORE,
   opAt 2829 .LT,
   opAt 2830 (.Swap ⟨1, by decide⟩),
   opAt 2831 .GT,
   opAt 2832 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2833 (.Dup ⟨0, by decide⟩),
   pushAt 2834 0 0,
   opAt 2835 .MLOAD,
   opAt 2836 .ADD,
   opAt 2837 (.Dup ⟨0, by decide⟩),
   pushAt 2838 2 2112,
   opAt 2839 .MLOAD,
   opAt 2840 (.Dup ⟨1, by decide⟩),
   opAt 2841 (.Dup ⟨1, by decide⟩),
   opAt 2842 .SUB,
   pushAt 2843 2 1792,
   opAt 2844 .MSTORE,
   opAt 2845 .LT,
   opAt 2846 (.Swap ⟨1, by decide⟩),
   opAt 2847 .GT,
   opAt 2848 .OR]

private theorem cycleAnchor : CycleSubmission.Artifact.artifact.instructionPC 2672 = 3447 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem fixedPC3777 : CycleSubmission.Artifact.artifact.instructionPC 2714 = 3500 := by
  rw [show (2714:Nat)=2672+(2714-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3778 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3693 := by
  rw [show (2855:Nat)=2672+(2855-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3779 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3696 := by
  rw [show (2856:Nat)=2672+(2856-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3787 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3697 := by
  rw [show (2857:Nat)=2672+(2857-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3788 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3702 := by
  rw [show (2861:Nat)=2672+(2861-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3789 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3703 := by
  rw [show (2862:Nat)=2672+(2862-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3790 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3704 := by
  rw [show (2863:Nat)=2672+(2863-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3791 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3705 := by
  rw [show (2864:Nat)=2672+(2864-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3792 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3706 := by
  rw [show (2865:Nat)=2672+(2865-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3793 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3707 := by
  rw [show (2866:Nat)=2672+(2866-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3794 : CycleSubmission.Artifact.artifact.instructionPC 2867 = 3710 := by
  rw [show (2867:Nat)=2672+(2867-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3795 : CycleSubmission.Artifact.artifact.instructionPC 2868 = 3713 := by
  rw [show (2868:Nat)=2672+(2868-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3796 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3714 := by
  rw [show (2869:Nat)=2672+(2869-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3797 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3715 := by
  rw [show (2870:Nat)=2672+(2870-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3798 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3715 := fixedPC3797

@[simp] theorem fixedPC3799 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3715 := fixedPC3797

@[simp] theorem fixedPC3800 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3716 := by
  rw [show (2871:Nat)=2672+(2871-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3801 : CycleSubmission.Artifact.artifact.instructionPC 2872 = 3717 := by
  rw [show (2872:Nat)=2672+(2872-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3802 : CycleSubmission.Artifact.artifact.instructionPC 2873 = 3718 := by
  rw [show (2873:Nat)=2672+(2873-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3803 : CycleSubmission.Artifact.artifact.instructionPC 2874 = 3721 := by
  rw [show (2874:Nat)=2672+(2874-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3804 : CycleSubmission.Artifact.artifact.instructionPC 2875 = 3724 := by
  rw [show (2875:Nat)=2672+(2875-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : CycleSubmission.Artifact.artifact.instructionPC 2715 = 3501 := by
  rw [show (2715:Nat)=2672+(2715-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3115 : CycleSubmission.Artifact.artifact.instructionPC 2716 = 3502 := by
  rw [show (2716:Nat)=2672+(2716-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3116 : CycleSubmission.Artifact.artifact.instructionPC 2717 = 3503 := by
  rw [show (2717:Nat)=2672+(2717-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3117 : CycleSubmission.Artifact.artifact.instructionPC 2718 = 3506 := by
  rw [show (2718:Nat)=2672+(2718-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3118 : CycleSubmission.Artifact.artifact.instructionPC 2719 = 3509 := by
  rw [show (2719:Nat)=2672+(2719-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3119 : CycleSubmission.Artifact.artifact.instructionPC 2720 = 3512 := by
  rw [show (2720:Nat)=2672+(2720-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3458 := by
  rw [show (2683:Nat)=2672+(2683-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3462 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3462 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2687 (by rfl)

@[simp] theorem fixedPC3805 : CycleSubmission.Artifact.artifact.instructionPC 2721 = 3513 := by
  rw [show (2721:Nat)=2672+(2721-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3806 : CycleSubmission.Artifact.artifact.instructionPC 2722 = 3515 := by
  rw [show (2722:Nat)=2672+(2722-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3807 : CycleSubmission.Artifact.artifact.instructionPC 2723 = 3516 := by
  rw [show (2723:Nat)=2672+(2723-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3808 : CycleSubmission.Artifact.artifact.instructionPC 2724 = 3519 := by
  rw [show (2724:Nat)=2672+(2724-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPCs8 : CycleSubmission.Artifact.artifact.instructionPC 2725 = 3520 := by
  rw [show (2725:Nat)=2672+(2725-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3809 : CycleSubmission.Artifact.artifact.instructionPC 2726 = 3521 := by
  rw [show (2726:Nat)=2672+(2726-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3810 : CycleSubmission.Artifact.artifact.instructionPC 2727 = 3524 := by
  rw [show (2727:Nat)=2672+(2727-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3811 : CycleSubmission.Artifact.artifact.instructionPC 2728 = 3525 := by
  rw [show (2728:Nat)=2672+(2728-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3812 : CycleSubmission.Artifact.artifact.instructionPC 2729 = 3527 := by
  rw [show (2729:Nat)=2672+(2729-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3813 : CycleSubmission.Artifact.artifact.instructionPC 2730 = 3528 := by
  rw [show (2730:Nat)=2672+(2730-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3814 : CycleSubmission.Artifact.artifact.instructionPC 2731 = 3529 := by
  rw [show (2731:Nat)=2672+(2731-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3815 : CycleSubmission.Artifact.artifact.instructionPC 2732 = 3530 := by
  rw [show (2732:Nat)=2672+(2732-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3816 : CycleSubmission.Artifact.artifact.instructionPC 2732 = 3530 := by
  rw [show (2732:Nat)=2672+(2732-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3817 : CycleSubmission.Artifact.artifact.instructionPC 2733 = 3531 := by
  rw [show (2733:Nat)=2672+(2733-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3818 : CycleSubmission.Artifact.artifact.instructionPC 2734 = 3534 := by
  rw [show (2734:Nat)=2672+(2734-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3819 : CycleSubmission.Artifact.artifact.instructionPC 2735 = 3535 := by
  rw [show (2735:Nat)=2672+(2735-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3820 : CycleSubmission.Artifact.artifact.instructionPC 2736 = 3536 := by
  rw [show (2736:Nat)=2672+(2736-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3821 : CycleSubmission.Artifact.artifact.instructionPC 2737 = 3537 := by
  rw [show (2737:Nat)=2672+(2737-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3822 : CycleSubmission.Artifact.artifact.instructionPC 2738 = 3539 := by
  rw [show (2738:Nat)=2672+(2738-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3823 : CycleSubmission.Artifact.artifact.instructionPC 2739 = 3540 := by
  rw [show (2739:Nat)=2672+(2739-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3824 : CycleSubmission.Artifact.artifact.instructionPC 2740 = 3541 := by
  rw [show (2740:Nat)=2672+(2740-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3825 : CycleSubmission.Artifact.artifact.instructionPC 2741 = 3542 := by
  rw [show (2741:Nat)=2672+(2741-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3826 : CycleSubmission.Artifact.artifact.instructionPC 2742 = 3545 := by
  rw [show (2742:Nat)=2672+(2742-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3827 : CycleSubmission.Artifact.artifact.instructionPC 2743 = 3546 := by
  rw [show (2743:Nat)=2672+(2743-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3828 : CycleSubmission.Artifact.artifact.instructionPC 2744 = 3547 := by
  rw [show (2744:Nat)=2672+(2744-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3829 : CycleSubmission.Artifact.artifact.instructionPC 2745 = 3548 := by
  rw [show (2745:Nat)=2672+(2745-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3830 : CycleSubmission.Artifact.artifact.instructionPC 2746 = 3549 := by
  rw [show (2746:Nat)=2672+(2746-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3831 : CycleSubmission.Artifact.artifact.instructionPC 2747 = 3552 := by
  rw [show (2747:Nat)=2672+(2747-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3832 : CycleSubmission.Artifact.artifact.instructionPC 2748 = 3553 := by
  rw [show (2748:Nat)=2672+(2748-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3833 : CycleSubmission.Artifact.artifact.instructionPC 2749 = 3554 := by
  rw [show (2749:Nat)=2672+(2749-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3834 : CycleSubmission.Artifact.artifact.instructionPC 2749 = 3554 := by
  rw [show (2749:Nat)=2672+(2749-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3835 : CycleSubmission.Artifact.artifact.instructionPC 2750 = 3555 := by
  rw [show (2750:Nat)=2672+(2750-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3836 : CycleSubmission.Artifact.artifact.instructionPC 2751 = 3556 := by
  rw [show (2751:Nat)=2672+(2751-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3837 : CycleSubmission.Artifact.artifact.instructionPC 2752 = 3557 := by
  rw [show (2752:Nat)=2672+(2752-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3838 : CycleSubmission.Artifact.artifact.instructionPC 2753 = 3558 := by
  rw [show (2753:Nat)=2672+(2753-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3839 : CycleSubmission.Artifact.artifact.instructionPC 2754 = 3560 := by
  rw [show (2754:Nat)=2672+(2754-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3840 : CycleSubmission.Artifact.artifact.instructionPC 2755 = 3561 := by
  rw [show (2755:Nat)=2672+(2755-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3841 : CycleSubmission.Artifact.artifact.instructionPC 2756 = 3562 := by
  rw [show (2756:Nat)=2672+(2756-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3842 : CycleSubmission.Artifact.artifact.instructionPC 2757 = 3563 := by
  rw [show (2757:Nat)=2672+(2757-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3843 : CycleSubmission.Artifact.artifact.instructionPC 2758 = 3566 := by
  rw [show (2758:Nat)=2672+(2758-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3844 : CycleSubmission.Artifact.artifact.instructionPC 2759 = 3567 := by
  rw [show (2759:Nat)=2672+(2759-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3845 : CycleSubmission.Artifact.artifact.instructionPC 2760 = 3568 := by
  rw [show (2760:Nat)=2672+(2760-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3846 : CycleSubmission.Artifact.artifact.instructionPC 2761 = 3569 := by
  rw [show (2761:Nat)=2672+(2761-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3847 : CycleSubmission.Artifact.artifact.instructionPC 2762 = 3570 := by
  rw [show (2762:Nat)=2672+(2762-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3848 : CycleSubmission.Artifact.artifact.instructionPC 2763 = 3573 := by
  rw [show (2763:Nat)=2672+(2763-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3849 : CycleSubmission.Artifact.artifact.instructionPC 2764 = 3574 := by
  rw [show (2764:Nat)=2672+(2764-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3850 : CycleSubmission.Artifact.artifact.instructionPC 2765 = 3575 := by
  rw [show (2765:Nat)=2672+(2765-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3851 : CycleSubmission.Artifact.artifact.instructionPC 2766 = 3576 := by
  rw [show (2766:Nat)=2672+(2766-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3852 : CycleSubmission.Artifact.artifact.instructionPC 2766 = 3576 := by
  rw [show (2766:Nat)=2672+(2766-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3853 : CycleSubmission.Artifact.artifact.instructionPC 2767 = 3577 := by
  rw [show (2767:Nat)=2672+(2767-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3854 : CycleSubmission.Artifact.artifact.instructionPC 2768 = 3578 := by
  rw [show (2768:Nat)=2672+(2768-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3855 : CycleSubmission.Artifact.artifact.instructionPC 2769 = 3579 := by
  rw [show (2769:Nat)=2672+(2769-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3856 : CycleSubmission.Artifact.artifact.instructionPC 2770 = 3581 := by
  rw [show (2770:Nat)=2672+(2770-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3857 : CycleSubmission.Artifact.artifact.instructionPC 2771 = 3582 := by
  rw [show (2771:Nat)=2672+(2771-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3858 : CycleSubmission.Artifact.artifact.instructionPC 2772 = 3583 := by
  rw [show (2772:Nat)=2672+(2772-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3859 : CycleSubmission.Artifact.artifact.instructionPC 2773 = 3584 := by
  rw [show (2773:Nat)=2672+(2773-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3860 : CycleSubmission.Artifact.artifact.instructionPC 2774 = 3587 := by
  rw [show (2774:Nat)=2672+(2774-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3861 : CycleSubmission.Artifact.artifact.instructionPC 2775 = 3588 := by
  rw [show (2775:Nat)=2672+(2775-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3862 : CycleSubmission.Artifact.artifact.instructionPC 2776 = 3589 := by
  rw [show (2776:Nat)=2672+(2776-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3863 : CycleSubmission.Artifact.artifact.instructionPC 2777 = 3590 := by
  rw [show (2777:Nat)=2672+(2777-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3864 : CycleSubmission.Artifact.artifact.instructionPC 2778 = 3591 := by
  rw [show (2778:Nat)=2672+(2778-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3865 : CycleSubmission.Artifact.artifact.instructionPC 2779 = 3594 := by
  rw [show (2779:Nat)=2672+(2779-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3866 : CycleSubmission.Artifact.artifact.instructionPC 2780 = 3595 := by
  rw [show (2780:Nat)=2672+(2780-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3867 : CycleSubmission.Artifact.artifact.instructionPC 2781 = 3596 := by
  rw [show (2781:Nat)=2672+(2781-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3868 : CycleSubmission.Artifact.artifact.instructionPC 2782 = 3597 := by
  rw [show (2782:Nat)=2672+(2782-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3869 : CycleSubmission.Artifact.artifact.instructionPC 2783 = 3598 := by
  rw [show (2783:Nat)=2672+(2783-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3871 : CycleSubmission.Artifact.artifact.instructionPC 2783 = 3598 := by
  rw [show (2783:Nat)=2672+(2783-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3872 : CycleSubmission.Artifact.artifact.instructionPC 2784 = 3599 := by
  rw [show (2784:Nat)=2672+(2784-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3873 : CycleSubmission.Artifact.artifact.instructionPC 2785 = 3600 := by
  rw [show (2785:Nat)=2672+(2785-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3874 : CycleSubmission.Artifact.artifact.instructionPC 2786 = 3602 := by
  rw [show (2786:Nat)=2672+(2786-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3875 : CycleSubmission.Artifact.artifact.instructionPC 2787 = 3603 := by
  rw [show (2787:Nat)=2672+(2787-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3876 : CycleSubmission.Artifact.artifact.instructionPC 2788 = 3604 := by
  rw [show (2788:Nat)=2672+(2788-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3877 : CycleSubmission.Artifact.artifact.instructionPC 2789 = 3605 := by
  rw [show (2789:Nat)=2672+(2789-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3878 : CycleSubmission.Artifact.artifact.instructionPC 2790 = 3608 := by
  rw [show (2790:Nat)=2672+(2790-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3879 : CycleSubmission.Artifact.artifact.instructionPC 2791 = 3609 := by
  rw [show (2791:Nat)=2672+(2791-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3880 : CycleSubmission.Artifact.artifact.instructionPC 2792 = 3610 := by
  rw [show (2792:Nat)=2672+(2792-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3881 : CycleSubmission.Artifact.artifact.instructionPC 2793 = 3611 := by
  rw [show (2793:Nat)=2672+(2793-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3882 : CycleSubmission.Artifact.artifact.instructionPC 2794 = 3612 := by
  rw [show (2794:Nat)=2672+(2794-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3883 : CycleSubmission.Artifact.artifact.instructionPC 2795 = 3615 := by
  rw [show (2795:Nat)=2672+(2795-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3884 : CycleSubmission.Artifact.artifact.instructionPC 2796 = 3616 := by
  rw [show (2796:Nat)=2672+(2796-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3885 : CycleSubmission.Artifact.artifact.instructionPC 2797 = 3617 := by
  rw [show (2797:Nat)=2672+(2797-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3886 : CycleSubmission.Artifact.artifact.instructionPC 2798 = 3618 := by
  rw [show (2798:Nat)=2672+(2798-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3887 : CycleSubmission.Artifact.artifact.instructionPC 2799 = 3619 := by
  rw [show (2799:Nat)=2672+(2799-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3888 : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3620 := by
  rw [show (2800:Nat)=2672+(2800-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3889 : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3620 := by
  rw [show (2800:Nat)=2672+(2800-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3620 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3620 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2800 (by rfl)

@[simp] theorem fixedPC3890 : CycleSubmission.Artifact.artifact.instructionPC 2801 = 3621 := by
  rw [show (2801:Nat)=2672+(2801-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3891 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3622 := by
  rw [show (2802:Nat)=2672+(2802-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3892 : CycleSubmission.Artifact.artifact.instructionPC 2803 = 3624 := by
  rw [show (2803:Nat)=2672+(2803-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3893 : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3625 := by
  rw [show (2804:Nat)=2672+(2804-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3894 : CycleSubmission.Artifact.artifact.instructionPC 2805 = 3626 := by
  rw [show (2805:Nat)=2672+(2805-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3895 : CycleSubmission.Artifact.artifact.instructionPC 2806 = 3627 := by
  rw [show (2806:Nat)=2672+(2806-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3896 : CycleSubmission.Artifact.artifact.instructionPC 2807 = 3630 := by
  rw [show (2807:Nat)=2672+(2807-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3897 : CycleSubmission.Artifact.artifact.instructionPC 2808 = 3631 := by
  rw [show (2808:Nat)=2672+(2808-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3898 : CycleSubmission.Artifact.artifact.instructionPC 2809 = 3632 := by
  rw [show (2809:Nat)=2672+(2809-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3899 : CycleSubmission.Artifact.artifact.instructionPC 2810 = 3633 := by
  rw [show (2810:Nat)=2672+(2810-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3900 : CycleSubmission.Artifact.artifact.instructionPC 2811 = 3634 := by
  rw [show (2811:Nat)=2672+(2811-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3901 : CycleSubmission.Artifact.artifact.instructionPC 2812 = 3637 := by
  rw [show (2812:Nat)=2672+(2812-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3902 : CycleSubmission.Artifact.artifact.instructionPC 2813 = 3638 := by
  rw [show (2813:Nat)=2672+(2813-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3903 : CycleSubmission.Artifact.artifact.instructionPC 2814 = 3639 := by
  rw [show (2814:Nat)=2672+(2814-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3904 : CycleSubmission.Artifact.artifact.instructionPC 2815 = 3640 := by
  rw [show (2815:Nat)=2672+(2815-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3905 : CycleSubmission.Artifact.artifact.instructionPC 2816 = 3641 := by
  rw [show (2816:Nat)=2672+(2816-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3906 : CycleSubmission.Artifact.artifact.instructionPC 2817 = 3642 := by
  rw [show (2817:Nat)=2672+(2817-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3907 : CycleSubmission.Artifact.artifact.instructionPC 2818 = 3643 := by
  rw [show (2818:Nat)=2672+(2818-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3908 : CycleSubmission.Artifact.artifact.instructionPC 2818 = 3643 := by
  rw [show (2818:Nat)=2672+(2818-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3909 : CycleSubmission.Artifact.artifact.instructionPC 2819 = 3645 := by
  rw [show (2819:Nat)=2672+(2819-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3910 : CycleSubmission.Artifact.artifact.instructionPC 2820 = 3646 := by
  rw [show (2820:Nat)=2672+(2820-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3911 : CycleSubmission.Artifact.artifact.instructionPC 2821 = 3647 := by
  rw [show (2821:Nat)=2672+(2821-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3912 : CycleSubmission.Artifact.artifact.instructionPC 2822 = 3648 := by
  rw [show (2822:Nat)=2672+(2822-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3913 : CycleSubmission.Artifact.artifact.instructionPC 2823 = 3651 := by
  rw [show (2823:Nat)=2672+(2823-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3914 : CycleSubmission.Artifact.artifact.instructionPC 2824 = 3652 := by
  rw [show (2824:Nat)=2672+(2824-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3915 : CycleSubmission.Artifact.artifact.instructionPC 2825 = 3653 := by
  rw [show (2825:Nat)=2672+(2825-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3916 : CycleSubmission.Artifact.artifact.instructionPC 2826 = 3654 := by
  rw [show (2826:Nat)=2672+(2826-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3917 : CycleSubmission.Artifact.artifact.instructionPC 2827 = 3655 := by
  rw [show (2827:Nat)=2672+(2827-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3918 : CycleSubmission.Artifact.artifact.instructionPC 2828 = 3658 := by
  rw [show (2828:Nat)=2672+(2828-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3919 : CycleSubmission.Artifact.artifact.instructionPC 2829 = 3659 := by
  rw [show (2829:Nat)=2672+(2829-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3920 : CycleSubmission.Artifact.artifact.instructionPC 2830 = 3660 := by
  rw [show (2830:Nat)=2672+(2830-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2831 = 3661 := by
  rw [show (2831:Nat)=2672+(2831-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2832 = 3662 := by
  rw [show (2832:Nat)=2672+(2832-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2833 = 3663 := by
  rw [show (2833:Nat)=2672+(2833-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2834 = 3664 := by
  rw [show (2834:Nat)=2672+(2834-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2835 = 3665 := by
  rw [show (2835:Nat)=2672+(2835-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2835 = 3665 := by
  rw [show (2835:Nat)=2672+(2835-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2836 = 3666 := by
  rw [show (2836:Nat)=2672+(2836-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2837 = 3667 := by
  rw [show (2837:Nat)=2672+(2837-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3929 : CycleSubmission.Artifact.artifact.instructionPC 2838 = 3668 := by
  rw [show (2838:Nat)=2672+(2838-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3930 : CycleSubmission.Artifact.artifact.instructionPC 2839 = 3671 := by
  rw [show (2839:Nat)=2672+(2839-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3931 : CycleSubmission.Artifact.artifact.instructionPC 2840 = 3672 := by
  rw [show (2840:Nat)=2672+(2840-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3932 : CycleSubmission.Artifact.artifact.instructionPC 2841 = 3673 := by
  rw [show (2841:Nat)=2672+(2841-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3933 : CycleSubmission.Artifact.artifact.instructionPC 2842 = 3674 := by
  rw [show (2842:Nat)=2672+(2842-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3934 : CycleSubmission.Artifact.artifact.instructionPC 2843 = 3675 := by
  rw [show (2843:Nat)=2672+(2843-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3935 : CycleSubmission.Artifact.artifact.instructionPC 2844 = 3678 := by
  rw [show (2844:Nat)=2672+(2844-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3936 : CycleSubmission.Artifact.artifact.instructionPC 2845 = 3679 := by
  rw [show (2845:Nat)=2672+(2845-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3937 : CycleSubmission.Artifact.artifact.instructionPC 2846 = 3680 := by
  rw [show (2846:Nat)=2672+(2846-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3938 : CycleSubmission.Artifact.artifact.instructionPC 2847 = 3681 := by
  rw [show (2847:Nat)=2672+(2847-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3939 : CycleSubmission.Artifact.artifact.instructionPC 2848 = 3682 := by
  rw [show (2848:Nat)=2672+(2848-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3940 : CycleSubmission.Artifact.artifact.instructionPC 2849 = 3683 := by
  rw [show (2849:Nat)=2672+(2849-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3941 : CycleSubmission.Artifact.artifact.instructionPC 2850 = 3684 := by
  rw [show (2850:Nat)=2672+(2850-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3942 : CycleSubmission.Artifact.artifact.instructionPC 2851 = 3687 := by
  rw [show (2851:Nat)=2672+(2851-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3943 : CycleSubmission.Artifact.artifact.instructionPC 2852 = 3688 := by
  rw [show (2852:Nat)=2672+(2852-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3944 : CycleSubmission.Artifact.artifact.instructionPC 2852 = 3688 := by
  rw [show (2852:Nat)=2672+(2852-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3945 : CycleSubmission.Artifact.artifact.instructionPC 2853 = 3689 := by
  rw [show (2853:Nat)=2672+(2853-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3946 : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3692 := by
  rw [show (2854:Nat)=2672+(2854-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3947 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3693 := by
  rw [show (2855:Nat)=2672+(2855-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3948 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3696 := by
  rw [show (2856:Nat)=2672+(2856-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3949 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3714 := by
  rw [show (2869:Nat)=2672+(2869-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3950 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3714 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3715 := by
  rw [show (2870:Nat)=2672+(2870-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3952 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3716 := by
  rw [show (2871:Nat)=2672+(2871-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3953 : CycleSubmission.Artifact.artifact.instructionPC 2872 = 3717 := by
  rw [show (2872:Nat)=2672+(2872-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3954 : CycleSubmission.Artifact.artifact.instructionPC 2873 = 3718 := by
  rw [show (2873:Nat)=2672+(2873-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3955 : CycleSubmission.Artifact.artifact.instructionPC 2874 = 3721 := by
  rw [show (2874:Nat)=2672+(2874-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3956 : CycleSubmission.Artifact.artifact.instructionPC 2875 = 3724 := by
  rw [show (2875:Nat)=2672+(2875-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3957 : CycleSubmission.Artifact.artifact.instructionPC 2876 = 3725 := by
  rw [show (2876:Nat)=2672+(2876-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4190 : CycleSubmission.Artifact.artifact.instructionPC 2697 = 3477 := by
  rw [show (2697:Nat)=2672+(2697-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4193 : CycleSubmission.Artifact.artifact.instructionPC 2698 = 3478 := by
  rw [show (2698:Nat)=2672+(2698-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4194 : CycleSubmission.Artifact.artifact.instructionPC 2699 = 3481 := by
  rw [show (2699:Nat)=2672+(2699-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4547 : CycleSubmission.Artifact.artifact.instructionPC 2877 = 3726 := by
  rw [show (2877:Nat)=2672+(2877-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4548 : CycleSubmission.Artifact.artifact.instructionPC 2878 = 3727 := by
  rw [show (2878:Nat)=2672+(2878-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC3999 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3458 := by
  rw [show (2683:Nat)=2672+(2683-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3462 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3462 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2687 (by rfl)

@[simp] theorem fixedPC4000 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3459 := by
  rw [show (2684:Nat)=2672+(2684-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4001 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3460 := by
  rw [show (2685:Nat)=2672+(2685-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4002 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3461 := by
  rw [show (2686:Nat)=2672+(2686-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4003 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3462 := by
  rw [show (2687:Nat)=2672+(2687-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4004 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3463 := by
  rw [show (2688:Nat)=2672+(2688-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4005 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3466 := by
  rw [show (2689:Nat)=2672+(2689-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4006 : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3467 := by
  rw [show (2690:Nat)=2672+(2690-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4007 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3469 := by
  rw [show (2691:Nat)=2672+(2691-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4008 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3470 := by
  rw [show (2692:Nat)=2672+(2692-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4009 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3471 := by
  rw [show (2693:Nat)=2672+(2693-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4010 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3472 := by
  rw [show (2694:Nat)=2672+(2694-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4011 : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3473 := by
  rw [show (2695:Nat)=2672+(2695-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4012 : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3476 := by
  rw [show (2696:Nat)=2672+(2696-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2883 : CycleSubmission.Artifact.artifact.instructionPC 2652 = 3423 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : CycleSubmission.Artifact.artifact.instructionPC 2653 = 3424 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : CycleSubmission.Artifact.artifact.instructionPC 2654 = 3425 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : CycleSubmission.Artifact.artifact.instructionPC 2655 = 3426 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : CycleSubmission.Artifact.artifact.instructionPC 2656 = 3427 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : CycleSubmission.Artifact.artifact.instructionPC 2657 = 3428 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2890 : CycleSubmission.Artifact.artifact.instructionPC 2658 = 3429 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2891 : CycleSubmission.Artifact.artifact.instructionPC 2659 = 3432 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2892 : CycleSubmission.Artifact.artifact.instructionPC 2660 = 3433 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2893 : CycleSubmission.Artifact.artifact.instructionPC 2660 = 3433 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2894 : CycleSubmission.Artifact.artifact.instructionPC 2661 = 3436 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2895 : CycleSubmission.Artifact.artifact.instructionPC 2662 = 3437 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2896 : CycleSubmission.Artifact.artifact.instructionPC 2682 = 3457 := by
  rw [show (2682:Nat)=2672+(2682-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2930 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3458 := by
  rw [show (2683:Nat)=2672+(2683-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2931 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3459 := by
  rw [show (2684:Nat)=2672+(2684-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2932 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3460 := by
  rw [show (2685:Nat)=2672+(2685-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2933 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3461 := by
  rw [show (2686:Nat)=2672+(2686-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2934 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3462 := by
  rw [show (2687:Nat)=2672+(2687-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2935 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3463 := by
  rw [show (2688:Nat)=2672+(2688-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2936 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3466 := by
  rw [show (2689:Nat)=2672+(2689-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2937 : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3467 := by
  rw [show (2690:Nat)=2672+(2690-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2938 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3469 := by
  rw [show (2691:Nat)=2672+(2691-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2939 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3470 := by
  rw [show (2692:Nat)=2672+(2692-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2940 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3471 := by
  rw [show (2693:Nat)=2672+(2693-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2941 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3472 := by
  rw [show (2694:Nat)=2672+(2694-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2942 : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3473 := by
  rw [show (2695:Nat)=2672+(2695-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2943 : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3476 := by
  rw [show (2696:Nat)=2672+(2696-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3702 := by
  rw [show (2861:Nat)=2672+(2861-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3703 := by
  rw [show (2862:Nat)=2672+(2862-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3704 := by
  rw [show (2863:Nat)=2672+(2863-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3705 := by
  rw [show (2864:Nat)=2672+(2864-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3706 := by
  rw [show (2865:Nat)=2672+(2865-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3707 := by
  rw [show (2866:Nat)=2672+(2866-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2867 = 3710 := by
  rw [show (2867:Nat)=2672+(2867-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2868 = 3713 := by
  rw [show (2868:Nat)=2672+(2868-2672) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

end CycleSubmission.Global.Fast
