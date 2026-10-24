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
  [opAt 2722 .JUMPDEST,
   pushAt 2723 2 2688,
   opAt 2724 .MLOAD,
   pushAt 2725 1 128,
   opAt 2726 .EQ,
   pushAt 2727 2 3462,
   opAt 2728 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2722 .JUMPDEST,
   pushAt 2723 2 2688,
   opAt 2724 .MLOAD,
   pushAt 2725 1 128,
   opAt 2726 .EQ,
   pushAt 2727 2 3462,
   opAt 2728 .JUMPI,
   opAt 2695 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2729 .JUMPDEST,
   pushAt 2730 2 2336,
   opAt 2731 .MLOAD,
   pushAt 2732 1 224,
   opAt 2733 .MLOAD,
   opAt 2734 (.Dup ⟨0, by decide⟩),
   opAt 2735 (.Dup ⟨2, by decide⟩),
   opAt 2736 .SUB,
   pushAt 2737 2 2016,
   opAt 2738 .MSTORE,
   opAt 2739 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2740 (.Dup ⟨0, by decide⟩),
   pushAt 2741 1 192,
   opAt 2742 .MLOAD,
   opAt 2743 .ADD,
   opAt 2744 (.Dup ⟨0, by decide⟩),
   pushAt 2745 2 2304,
   opAt 2746 .MLOAD,
   opAt 2747 (.Dup ⟨1, by decide⟩),
   opAt 2748 (.Dup ⟨1, by decide⟩),
   opAt 2749 .SUB,
   pushAt 2750 2 1984,
   opAt 2751 .MSTORE,
   opAt 2752 .LT,
   opAt 2753 (.Swap ⟨1, by decide⟩),
   opAt 2754 .GT,
   opAt 2755 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2756 (.Dup ⟨0, by decide⟩),
   pushAt 2757 1 160,
   opAt 2758 .MLOAD,
   opAt 2759 .ADD,
   opAt 2760 (.Dup ⟨0, by decide⟩),
   pushAt 2761 2 2272,
   opAt 2762 .MLOAD,
   opAt 2763 (.Dup ⟨1, by decide⟩),
   opAt 2764 (.Dup ⟨1, by decide⟩),
   opAt 2765 .SUB,
   pushAt 2766 2 1952,
   opAt 2767 .MSTORE,
   opAt 2768 .LT,
   opAt 2769 (.Swap ⟨1, by decide⟩),
   opAt 2770 .GT,
   opAt 2771 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2772 (.Dup ⟨0, by decide⟩),
   pushAt 2773 1 128,
   opAt 2774 .MLOAD,
   opAt 2775 .ADD,
   opAt 2776 (.Dup ⟨0, by decide⟩),
   pushAt 2777 2 2240,
   opAt 2778 .MLOAD,
   opAt 2779 (.Dup ⟨1, by decide⟩),
   opAt 2780 (.Dup ⟨1, by decide⟩),
   opAt 2781 .SUB,
   pushAt 2782 2 1920,
   opAt 2783 .MSTORE,
   opAt 2784 .LT,
   opAt 2785 (.Swap ⟨1, by decide⟩),
   opAt 2786 .GT,
   opAt 2787 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2788 (.Dup ⟨0, by decide⟩),
   pushAt 2789 1 96,
   opAt 2790 .MLOAD,
   opAt 2791 .ADD,
   opAt 2792 (.Dup ⟨0, by decide⟩),
   pushAt 2793 2 2208,
   opAt 2794 .MLOAD,
   opAt 2795 (.Dup ⟨1, by decide⟩),
   opAt 2796 (.Dup ⟨1, by decide⟩),
   opAt 2797 .SUB,
   pushAt 2798 2 1888,
   opAt 2799 .MSTORE,
   opAt 2800 .LT,
   opAt 2801 (.Swap ⟨1, by decide⟩),
   opAt 2802 .GT,
   opAt 2803 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2804 .JUMPDEST,
   opAt 2805 (.Dup ⟨0, by decide⟩),
   pushAt 2806 1 64,
   opAt 2807 .MLOAD,
   opAt 2808 .ADD,
   opAt 2809 (.Dup ⟨0, by decide⟩),
   pushAt 2810 2 2176,
   opAt 2811 .MLOAD,
   opAt 2812 (.Dup ⟨1, by decide⟩),
   opAt 2813 (.Dup ⟨1, by decide⟩),
   opAt 2814 .SUB,
   pushAt 2815 2 1856,
   opAt 2816 .MSTORE,
   opAt 2817 .LT,
   opAt 2818 (.Swap ⟨1, by decide⟩),
   opAt 2819 .GT,
   opAt 2820 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2821 (.Dup ⟨0, by decide⟩),
   pushAt 2822 1 32,
   opAt 2823 .MLOAD,
   opAt 2824 .ADD,
   opAt 2825 (.Dup ⟨0, by decide⟩),
   pushAt 2826 2 2144,
   opAt 2827 .MLOAD,
   opAt 2828 (.Dup ⟨1, by decide⟩),
   opAt 2829 (.Dup ⟨1, by decide⟩),
   opAt 2830 .SUB,
   pushAt 2831 2 1824,
   opAt 2832 .MSTORE,
   opAt 2833 .LT,
   opAt 2834 (.Swap ⟨1, by decide⟩),
   opAt 2835 .GT,
   opAt 2836 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2837 (.Dup ⟨0, by decide⟩),
   pushAt 2838 0 0,
   opAt 2839 .MLOAD,
   opAt 2840 .ADD,
   opAt 2841 (.Dup ⟨0, by decide⟩),
   pushAt 2842 2 2112,
   opAt 2843 .MLOAD,
   opAt 2844 (.Dup ⟨1, by decide⟩),
   opAt 2845 (.Dup ⟨1, by decide⟩),
   opAt 2846 .SUB,
   pushAt 2847 2 1792,
   opAt 2848 .MSTORE,
   opAt 2849 .LT,
   opAt 2850 (.Swap ⟨1, by decide⟩),
   opAt 2851 .GT,
   opAt 2852 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2853 .ISZERO,
   pushAt 2854 2 2080,
   opAt 2855 .MLOAD,
   opAt 2856 .OR,
   pushAt 2857 2 3717,
   opAt 2858 .JUMPI,
   opAt 2873 .JUMPDEST,
   pushAt 2874 2 1792,
   pushAt 2875 2 2688,
   opAt 2876 .MLOAD,
   opAt 2877 (.Swap ⟨1, by decide⟩),
   opAt 2878 .MCOPY,
   opAt 2879 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2853 .ISZERO,
   pushAt 2854 2 2080,
   opAt 2855 .MLOAD,
   opAt 2856 .OR,
   pushAt 2857 2 3717,
   opAt 2858 .JUMPI,
   pushAt 2859 2 3706,
   opAt 2860 .JUMP,
   opAt 2866 .JUMPDEST,
   pushAt 2867 2 2112,
   pushAt 2868 2 2688,
   opAt 2869 .MLOAD,
   opAt 2870 (.Swap ⟨1, by decide⟩),
   opAt 2871 .MCOPY,
   opAt 2872 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2696 2 2208,
   opAt 2697 .MLOAD,
   pushAt 2698 1 96,
   opAt 2699 .MLOAD,
   opAt 2700 (.Dup ⟨0, by decide⟩),
   opAt 2701 (.Dup ⟨2, by decide⟩),
   opAt 2702 .SUB,
   pushAt 2703 2 1888,
   opAt 2704 .MSTORE,
   opAt 2705 .GT,
   pushAt 2706 2 3620,
   opAt 2707 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2804 .JUMPDEST,
   opAt 2805 (.Dup ⟨0, by decide⟩),
   pushAt 2806 1 64,
   opAt 2807 .MLOAD,
   opAt 2808 .ADD,
   opAt 2809 (.Dup ⟨0, by decide⟩),
   pushAt 2810 2 2176,
   opAt 2811 .MLOAD,
   opAt 2812 (.Dup ⟨1, by decide⟩),
   opAt 2813 (.Dup ⟨1, by decide⟩),
   opAt 2814 .SUB,
   pushAt 2815 2 1856,
   opAt 2816 .MSTORE,
   opAt 2817 .LT,
   opAt 2818 (.Swap ⟨1, by decide⟩),
   opAt 2819 .GT,
   opAt 2820 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2821 (.Dup ⟨0, by decide⟩),
   pushAt 2822 1 32,
   opAt 2823 .MLOAD,
   opAt 2824 .ADD,
   opAt 2825 (.Dup ⟨0, by decide⟩),
   pushAt 2826 2 2144,
   opAt 2827 .MLOAD,
   opAt 2828 (.Dup ⟨1, by decide⟩),
   opAt 2829 (.Dup ⟨1, by decide⟩),
   opAt 2830 .SUB,
   pushAt 2831 2 1824,
   opAt 2832 .MSTORE,
   opAt 2833 .LT,
   opAt 2834 (.Swap ⟨1, by decide⟩),
   opAt 2835 .GT,
   opAt 2836 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2837 (.Dup ⟨0, by decide⟩),
   pushAt 2838 0 0,
   opAt 2839 .MLOAD,
   opAt 2840 .ADD,
   opAt 2841 (.Dup ⟨0, by decide⟩),
   pushAt 2842 2 2112,
   opAt 2843 .MLOAD,
   opAt 2844 (.Dup ⟨1, by decide⟩),
   opAt 2845 (.Dup ⟨1, by decide⟩),
   opAt 2846 .SUB,
   pushAt 2847 2 1792,
   opAt 2848 .MSTORE,
   opAt 2849 .LT,
   opAt 2850 (.Swap ⟨1, by decide⟩),
   opAt 2851 .GT,
   opAt 2852 .OR]

private theorem cycleAnchor : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3442 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem fixedPC3777 : CycleSubmission.Artifact.artifact.instructionPC 2718 = 3500 := by
  rw [show (2718:Nat)=2683+(2718-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3508 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2722 = 3508 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2722 (by rfl)

@[simp] theorem fixedPC3778 : CycleSubmission.Artifact.artifact.instructionPC 2859 = 3693 := by
  rw [show (2859:Nat)=2683+(2859-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3779 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3696 := by
  rw [show (2860:Nat)=2683+(2860-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3787 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3697 := by
  rw [show (2861:Nat)=2683+(2861-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3788 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3698 := by
  rw [show (2862:Nat)=2683+(2862-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3789 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3701 := by
  rw [show (2863:Nat)=2683+(2863-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3790 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3702 := by
  rw [show (2864:Nat)=2683+(2864-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3791 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3705 := by
  rw [show (2865:Nat)=2683+(2865-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3792 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3706 := by
  rw [show (2866:Nat)=2683+(2866-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3793 : CycleSubmission.Artifact.artifact.instructionPC 2867 = 3707 := by
  rw [show (2867:Nat)=2683+(2867-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3794 : CycleSubmission.Artifact.artifact.instructionPC 2868 = 3710 := by
  rw [show (2868:Nat)=2683+(2868-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3795 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3713 := by
  rw [show (2869:Nat)=2683+(2869-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3796 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3714 := by
  rw [show (2870:Nat)=2683+(2870-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3797 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3715 := by
  rw [show (2871:Nat)=2683+(2871-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3798 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3715 := fixedPC3797

@[simp] theorem fixedPC3799 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3715 := fixedPC3797

@[simp] theorem fixedPC3800 : CycleSubmission.Artifact.artifact.instructionPC 2872 = 3716 := by
  rw [show (2872:Nat)=2683+(2872-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3801 : CycleSubmission.Artifact.artifact.instructionPC 2873 = 3717 := by
  rw [show (2873:Nat)=2683+(2873-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3802 : CycleSubmission.Artifact.artifact.instructionPC 2874 = 3718 := by
  rw [show (2874:Nat)=2683+(2874-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3803 : CycleSubmission.Artifact.artifact.instructionPC 2875 = 3721 := by
  rw [show (2875:Nat)=2683+(2875-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3804 : CycleSubmission.Artifact.artifact.instructionPC 2876 = 3724 := by
  rw [show (2876:Nat)=2683+(2876-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : CycleSubmission.Artifact.artifact.instructionPC 2719 = 3501 := by
  rw [show (2719:Nat)=2683+(2719-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3115 : CycleSubmission.Artifact.artifact.instructionPC 2720 = 3504 := by
  rw [show (2720:Nat)=2683+(2720-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3116 : CycleSubmission.Artifact.artifact.instructionPC 2721 = 3505 := by
  rw [show (2721:Nat)=2683+(2721-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3117 : CycleSubmission.Artifact.artifact.instructionPC 2722 = 3508 := by
  rw [show (2722:Nat)=2683+(2722-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3118 : CycleSubmission.Artifact.artifact.instructionPC 2723 = 3509 := by
  rw [show (2723:Nat)=2683+(2723-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3119 : CycleSubmission.Artifact.artifact.instructionPC 2724 = 3512 := by
  rw [show (2724:Nat)=2683+(2724-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3454 := by
  rw [show (2691:Nat)=2683+(2691-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3462 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3462 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2695 (by rfl)

@[simp] theorem fixedPC3805 : CycleSubmission.Artifact.artifact.instructionPC 2725 = 3513 := by
  rw [show (2725:Nat)=2683+(2725-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3806 : CycleSubmission.Artifact.artifact.instructionPC 2726 = 3515 := by
  rw [show (2726:Nat)=2683+(2726-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3807 : CycleSubmission.Artifact.artifact.instructionPC 2727 = 3516 := by
  rw [show (2727:Nat)=2683+(2727-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3808 : CycleSubmission.Artifact.artifact.instructionPC 2728 = 3519 := by
  rw [show (2728:Nat)=2683+(2728-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPCs8 : CycleSubmission.Artifact.artifact.instructionPC 2729 = 3520 := by
  rw [show (2729:Nat)=2683+(2729-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3809 : CycleSubmission.Artifact.artifact.instructionPC 2730 = 3521 := by
  rw [show (2730:Nat)=2683+(2730-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3810 : CycleSubmission.Artifact.artifact.instructionPC 2731 = 3524 := by
  rw [show (2731:Nat)=2683+(2731-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3811 : CycleSubmission.Artifact.artifact.instructionPC 2732 = 3525 := by
  rw [show (2732:Nat)=2683+(2732-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3812 : CycleSubmission.Artifact.artifact.instructionPC 2733 = 3527 := by
  rw [show (2733:Nat)=2683+(2733-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3813 : CycleSubmission.Artifact.artifact.instructionPC 2734 = 3528 := by
  rw [show (2734:Nat)=2683+(2734-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3814 : CycleSubmission.Artifact.artifact.instructionPC 2735 = 3529 := by
  rw [show (2735:Nat)=2683+(2735-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3815 : CycleSubmission.Artifact.artifact.instructionPC 2736 = 3530 := by
  rw [show (2736:Nat)=2683+(2736-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3816 : CycleSubmission.Artifact.artifact.instructionPC 2736 = 3530 := by
  rw [show (2736:Nat)=2683+(2736-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3817 : CycleSubmission.Artifact.artifact.instructionPC 2737 = 3531 := by
  rw [show (2737:Nat)=2683+(2737-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3818 : CycleSubmission.Artifact.artifact.instructionPC 2738 = 3534 := by
  rw [show (2738:Nat)=2683+(2738-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3819 : CycleSubmission.Artifact.artifact.instructionPC 2739 = 3535 := by
  rw [show (2739:Nat)=2683+(2739-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3820 : CycleSubmission.Artifact.artifact.instructionPC 2740 = 3536 := by
  rw [show (2740:Nat)=2683+(2740-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3821 : CycleSubmission.Artifact.artifact.instructionPC 2741 = 3537 := by
  rw [show (2741:Nat)=2683+(2741-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3822 : CycleSubmission.Artifact.artifact.instructionPC 2742 = 3539 := by
  rw [show (2742:Nat)=2683+(2742-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3823 : CycleSubmission.Artifact.artifact.instructionPC 2743 = 3540 := by
  rw [show (2743:Nat)=2683+(2743-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3824 : CycleSubmission.Artifact.artifact.instructionPC 2744 = 3541 := by
  rw [show (2744:Nat)=2683+(2744-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3825 : CycleSubmission.Artifact.artifact.instructionPC 2745 = 3542 := by
  rw [show (2745:Nat)=2683+(2745-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3826 : CycleSubmission.Artifact.artifact.instructionPC 2746 = 3545 := by
  rw [show (2746:Nat)=2683+(2746-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3827 : CycleSubmission.Artifact.artifact.instructionPC 2747 = 3546 := by
  rw [show (2747:Nat)=2683+(2747-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3828 : CycleSubmission.Artifact.artifact.instructionPC 2748 = 3547 := by
  rw [show (2748:Nat)=2683+(2748-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3829 : CycleSubmission.Artifact.artifact.instructionPC 2749 = 3548 := by
  rw [show (2749:Nat)=2683+(2749-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3830 : CycleSubmission.Artifact.artifact.instructionPC 2750 = 3549 := by
  rw [show (2750:Nat)=2683+(2750-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3831 : CycleSubmission.Artifact.artifact.instructionPC 2751 = 3552 := by
  rw [show (2751:Nat)=2683+(2751-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3832 : CycleSubmission.Artifact.artifact.instructionPC 2752 = 3553 := by
  rw [show (2752:Nat)=2683+(2752-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3833 : CycleSubmission.Artifact.artifact.instructionPC 2753 = 3554 := by
  rw [show (2753:Nat)=2683+(2753-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3834 : CycleSubmission.Artifact.artifact.instructionPC 2753 = 3554 := by
  rw [show (2753:Nat)=2683+(2753-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3835 : CycleSubmission.Artifact.artifact.instructionPC 2754 = 3555 := by
  rw [show (2754:Nat)=2683+(2754-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3836 : CycleSubmission.Artifact.artifact.instructionPC 2755 = 3556 := by
  rw [show (2755:Nat)=2683+(2755-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3837 : CycleSubmission.Artifact.artifact.instructionPC 2756 = 3557 := by
  rw [show (2756:Nat)=2683+(2756-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3838 : CycleSubmission.Artifact.artifact.instructionPC 2757 = 3558 := by
  rw [show (2757:Nat)=2683+(2757-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3839 : CycleSubmission.Artifact.artifact.instructionPC 2758 = 3560 := by
  rw [show (2758:Nat)=2683+(2758-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3840 : CycleSubmission.Artifact.artifact.instructionPC 2759 = 3561 := by
  rw [show (2759:Nat)=2683+(2759-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3841 : CycleSubmission.Artifact.artifact.instructionPC 2760 = 3562 := by
  rw [show (2760:Nat)=2683+(2760-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3842 : CycleSubmission.Artifact.artifact.instructionPC 2761 = 3563 := by
  rw [show (2761:Nat)=2683+(2761-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3843 : CycleSubmission.Artifact.artifact.instructionPC 2762 = 3566 := by
  rw [show (2762:Nat)=2683+(2762-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3844 : CycleSubmission.Artifact.artifact.instructionPC 2763 = 3567 := by
  rw [show (2763:Nat)=2683+(2763-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3845 : CycleSubmission.Artifact.artifact.instructionPC 2764 = 3568 := by
  rw [show (2764:Nat)=2683+(2764-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3846 : CycleSubmission.Artifact.artifact.instructionPC 2765 = 3569 := by
  rw [show (2765:Nat)=2683+(2765-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3847 : CycleSubmission.Artifact.artifact.instructionPC 2766 = 3570 := by
  rw [show (2766:Nat)=2683+(2766-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3848 : CycleSubmission.Artifact.artifact.instructionPC 2767 = 3573 := by
  rw [show (2767:Nat)=2683+(2767-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3849 : CycleSubmission.Artifact.artifact.instructionPC 2768 = 3574 := by
  rw [show (2768:Nat)=2683+(2768-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3850 : CycleSubmission.Artifact.artifact.instructionPC 2769 = 3575 := by
  rw [show (2769:Nat)=2683+(2769-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3851 : CycleSubmission.Artifact.artifact.instructionPC 2770 = 3576 := by
  rw [show (2770:Nat)=2683+(2770-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3852 : CycleSubmission.Artifact.artifact.instructionPC 2770 = 3576 := by
  rw [show (2770:Nat)=2683+(2770-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3853 : CycleSubmission.Artifact.artifact.instructionPC 2771 = 3577 := by
  rw [show (2771:Nat)=2683+(2771-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3854 : CycleSubmission.Artifact.artifact.instructionPC 2772 = 3578 := by
  rw [show (2772:Nat)=2683+(2772-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3855 : CycleSubmission.Artifact.artifact.instructionPC 2773 = 3579 := by
  rw [show (2773:Nat)=2683+(2773-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3856 : CycleSubmission.Artifact.artifact.instructionPC 2774 = 3581 := by
  rw [show (2774:Nat)=2683+(2774-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3857 : CycleSubmission.Artifact.artifact.instructionPC 2775 = 3582 := by
  rw [show (2775:Nat)=2683+(2775-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3858 : CycleSubmission.Artifact.artifact.instructionPC 2776 = 3583 := by
  rw [show (2776:Nat)=2683+(2776-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3859 : CycleSubmission.Artifact.artifact.instructionPC 2777 = 3584 := by
  rw [show (2777:Nat)=2683+(2777-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3860 : CycleSubmission.Artifact.artifact.instructionPC 2778 = 3587 := by
  rw [show (2778:Nat)=2683+(2778-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3861 : CycleSubmission.Artifact.artifact.instructionPC 2779 = 3588 := by
  rw [show (2779:Nat)=2683+(2779-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3862 : CycleSubmission.Artifact.artifact.instructionPC 2780 = 3589 := by
  rw [show (2780:Nat)=2683+(2780-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3863 : CycleSubmission.Artifact.artifact.instructionPC 2781 = 3590 := by
  rw [show (2781:Nat)=2683+(2781-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3864 : CycleSubmission.Artifact.artifact.instructionPC 2782 = 3591 := by
  rw [show (2782:Nat)=2683+(2782-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3865 : CycleSubmission.Artifact.artifact.instructionPC 2783 = 3594 := by
  rw [show (2783:Nat)=2683+(2783-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3866 : CycleSubmission.Artifact.artifact.instructionPC 2784 = 3595 := by
  rw [show (2784:Nat)=2683+(2784-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3867 : CycleSubmission.Artifact.artifact.instructionPC 2785 = 3596 := by
  rw [show (2785:Nat)=2683+(2785-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3868 : CycleSubmission.Artifact.artifact.instructionPC 2786 = 3597 := by
  rw [show (2786:Nat)=2683+(2786-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3869 : CycleSubmission.Artifact.artifact.instructionPC 2787 = 3598 := by
  rw [show (2787:Nat)=2683+(2787-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3871 : CycleSubmission.Artifact.artifact.instructionPC 2787 = 3598 := by
  rw [show (2787:Nat)=2683+(2787-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3872 : CycleSubmission.Artifact.artifact.instructionPC 2788 = 3599 := by
  rw [show (2788:Nat)=2683+(2788-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3873 : CycleSubmission.Artifact.artifact.instructionPC 2789 = 3600 := by
  rw [show (2789:Nat)=2683+(2789-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3874 : CycleSubmission.Artifact.artifact.instructionPC 2790 = 3602 := by
  rw [show (2790:Nat)=2683+(2790-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3875 : CycleSubmission.Artifact.artifact.instructionPC 2791 = 3603 := by
  rw [show (2791:Nat)=2683+(2791-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3876 : CycleSubmission.Artifact.artifact.instructionPC 2792 = 3604 := by
  rw [show (2792:Nat)=2683+(2792-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3877 : CycleSubmission.Artifact.artifact.instructionPC 2793 = 3605 := by
  rw [show (2793:Nat)=2683+(2793-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3878 : CycleSubmission.Artifact.artifact.instructionPC 2794 = 3608 := by
  rw [show (2794:Nat)=2683+(2794-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3879 : CycleSubmission.Artifact.artifact.instructionPC 2795 = 3609 := by
  rw [show (2795:Nat)=2683+(2795-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3880 : CycleSubmission.Artifact.artifact.instructionPC 2796 = 3610 := by
  rw [show (2796:Nat)=2683+(2796-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3881 : CycleSubmission.Artifact.artifact.instructionPC 2797 = 3611 := by
  rw [show (2797:Nat)=2683+(2797-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3882 : CycleSubmission.Artifact.artifact.instructionPC 2798 = 3612 := by
  rw [show (2798:Nat)=2683+(2798-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3883 : CycleSubmission.Artifact.artifact.instructionPC 2799 = 3615 := by
  rw [show (2799:Nat)=2683+(2799-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3884 : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3616 := by
  rw [show (2800:Nat)=2683+(2800-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3885 : CycleSubmission.Artifact.artifact.instructionPC 2801 = 3617 := by
  rw [show (2801:Nat)=2683+(2801-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3886 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3618 := by
  rw [show (2802:Nat)=2683+(2802-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3887 : CycleSubmission.Artifact.artifact.instructionPC 2803 = 3619 := by
  rw [show (2803:Nat)=2683+(2803-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3888 : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3620 := by
  rw [show (2804:Nat)=2683+(2804-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3889 : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3620 := by
  rw [show (2804:Nat)=2683+(2804-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3620 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3620 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2804 (by rfl)

@[simp] theorem fixedPC3890 : CycleSubmission.Artifact.artifact.instructionPC 2805 = 3621 := by
  rw [show (2805:Nat)=2683+(2805-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3891 : CycleSubmission.Artifact.artifact.instructionPC 2806 = 3622 := by
  rw [show (2806:Nat)=2683+(2806-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3892 : CycleSubmission.Artifact.artifact.instructionPC 2807 = 3624 := by
  rw [show (2807:Nat)=2683+(2807-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3893 : CycleSubmission.Artifact.artifact.instructionPC 2808 = 3625 := by
  rw [show (2808:Nat)=2683+(2808-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3894 : CycleSubmission.Artifact.artifact.instructionPC 2809 = 3626 := by
  rw [show (2809:Nat)=2683+(2809-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3895 : CycleSubmission.Artifact.artifact.instructionPC 2810 = 3627 := by
  rw [show (2810:Nat)=2683+(2810-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3896 : CycleSubmission.Artifact.artifact.instructionPC 2811 = 3630 := by
  rw [show (2811:Nat)=2683+(2811-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3897 : CycleSubmission.Artifact.artifact.instructionPC 2812 = 3631 := by
  rw [show (2812:Nat)=2683+(2812-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3898 : CycleSubmission.Artifact.artifact.instructionPC 2813 = 3632 := by
  rw [show (2813:Nat)=2683+(2813-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3899 : CycleSubmission.Artifact.artifact.instructionPC 2814 = 3633 := by
  rw [show (2814:Nat)=2683+(2814-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3900 : CycleSubmission.Artifact.artifact.instructionPC 2815 = 3634 := by
  rw [show (2815:Nat)=2683+(2815-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3901 : CycleSubmission.Artifact.artifact.instructionPC 2816 = 3637 := by
  rw [show (2816:Nat)=2683+(2816-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3902 : CycleSubmission.Artifact.artifact.instructionPC 2817 = 3638 := by
  rw [show (2817:Nat)=2683+(2817-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3903 : CycleSubmission.Artifact.artifact.instructionPC 2818 = 3639 := by
  rw [show (2818:Nat)=2683+(2818-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3904 : CycleSubmission.Artifact.artifact.instructionPC 2819 = 3640 := by
  rw [show (2819:Nat)=2683+(2819-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3905 : CycleSubmission.Artifact.artifact.instructionPC 2820 = 3641 := by
  rw [show (2820:Nat)=2683+(2820-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3906 : CycleSubmission.Artifact.artifact.instructionPC 2821 = 3642 := by
  rw [show (2821:Nat)=2683+(2821-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3907 : CycleSubmission.Artifact.artifact.instructionPC 2822 = 3643 := by
  rw [show (2822:Nat)=2683+(2822-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3908 : CycleSubmission.Artifact.artifact.instructionPC 2822 = 3643 := by
  rw [show (2822:Nat)=2683+(2822-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3909 : CycleSubmission.Artifact.artifact.instructionPC 2823 = 3645 := by
  rw [show (2823:Nat)=2683+(2823-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3910 : CycleSubmission.Artifact.artifact.instructionPC 2824 = 3646 := by
  rw [show (2824:Nat)=2683+(2824-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3911 : CycleSubmission.Artifact.artifact.instructionPC 2825 = 3647 := by
  rw [show (2825:Nat)=2683+(2825-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3912 : CycleSubmission.Artifact.artifact.instructionPC 2826 = 3648 := by
  rw [show (2826:Nat)=2683+(2826-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3913 : CycleSubmission.Artifact.artifact.instructionPC 2827 = 3651 := by
  rw [show (2827:Nat)=2683+(2827-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3914 : CycleSubmission.Artifact.artifact.instructionPC 2828 = 3652 := by
  rw [show (2828:Nat)=2683+(2828-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3915 : CycleSubmission.Artifact.artifact.instructionPC 2829 = 3653 := by
  rw [show (2829:Nat)=2683+(2829-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3916 : CycleSubmission.Artifact.artifact.instructionPC 2830 = 3654 := by
  rw [show (2830:Nat)=2683+(2830-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3917 : CycleSubmission.Artifact.artifact.instructionPC 2831 = 3655 := by
  rw [show (2831:Nat)=2683+(2831-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3918 : CycleSubmission.Artifact.artifact.instructionPC 2832 = 3658 := by
  rw [show (2832:Nat)=2683+(2832-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3919 : CycleSubmission.Artifact.artifact.instructionPC 2833 = 3659 := by
  rw [show (2833:Nat)=2683+(2833-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3920 : CycleSubmission.Artifact.artifact.instructionPC 2834 = 3660 := by
  rw [show (2834:Nat)=2683+(2834-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2835 = 3661 := by
  rw [show (2835:Nat)=2683+(2835-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2836 = 3662 := by
  rw [show (2836:Nat)=2683+(2836-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2837 = 3663 := by
  rw [show (2837:Nat)=2683+(2837-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2838 = 3664 := by
  rw [show (2838:Nat)=2683+(2838-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2839 = 3665 := by
  rw [show (2839:Nat)=2683+(2839-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2839 = 3665 := by
  rw [show (2839:Nat)=2683+(2839-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2840 = 3666 := by
  rw [show (2840:Nat)=2683+(2840-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2841 = 3667 := by
  rw [show (2841:Nat)=2683+(2841-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3929 : CycleSubmission.Artifact.artifact.instructionPC 2842 = 3668 := by
  rw [show (2842:Nat)=2683+(2842-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3930 : CycleSubmission.Artifact.artifact.instructionPC 2843 = 3671 := by
  rw [show (2843:Nat)=2683+(2843-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3931 : CycleSubmission.Artifact.artifact.instructionPC 2844 = 3672 := by
  rw [show (2844:Nat)=2683+(2844-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3932 : CycleSubmission.Artifact.artifact.instructionPC 2845 = 3673 := by
  rw [show (2845:Nat)=2683+(2845-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3933 : CycleSubmission.Artifact.artifact.instructionPC 2846 = 3674 := by
  rw [show (2846:Nat)=2683+(2846-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3934 : CycleSubmission.Artifact.artifact.instructionPC 2847 = 3675 := by
  rw [show (2847:Nat)=2683+(2847-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3935 : CycleSubmission.Artifact.artifact.instructionPC 2848 = 3678 := by
  rw [show (2848:Nat)=2683+(2848-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3936 : CycleSubmission.Artifact.artifact.instructionPC 2849 = 3679 := by
  rw [show (2849:Nat)=2683+(2849-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3937 : CycleSubmission.Artifact.artifact.instructionPC 2850 = 3680 := by
  rw [show (2850:Nat)=2683+(2850-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3938 : CycleSubmission.Artifact.artifact.instructionPC 2851 = 3681 := by
  rw [show (2851:Nat)=2683+(2851-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3939 : CycleSubmission.Artifact.artifact.instructionPC 2852 = 3682 := by
  rw [show (2852:Nat)=2683+(2852-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3940 : CycleSubmission.Artifact.artifact.instructionPC 2853 = 3683 := by
  rw [show (2853:Nat)=2683+(2853-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3941 : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3684 := by
  rw [show (2854:Nat)=2683+(2854-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3942 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3687 := by
  rw [show (2855:Nat)=2683+(2855-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3943 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3688 := by
  rw [show (2856:Nat)=2683+(2856-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3944 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3688 := by
  rw [show (2856:Nat)=2683+(2856-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3945 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3689 := by
  rw [show (2857:Nat)=2683+(2857-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3946 : CycleSubmission.Artifact.artifact.instructionPC 2858 = 3692 := by
  rw [show (2858:Nat)=2683+(2858-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3947 : CycleSubmission.Artifact.artifact.instructionPC 2859 = 3693 := by
  rw [show (2859:Nat)=2683+(2859-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3948 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3696 := by
  rw [show (2860:Nat)=2683+(2860-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3949 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3714 := by
  rw [show (2870:Nat)=2683+(2870-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3950 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3714 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3715 := by
  rw [show (2871:Nat)=2683+(2871-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3952 : CycleSubmission.Artifact.artifact.instructionPC 2872 = 3716 := by
  rw [show (2872:Nat)=2683+(2872-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3953 : CycleSubmission.Artifact.artifact.instructionPC 2873 = 3717 := by
  rw [show (2873:Nat)=2683+(2873-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3954 : CycleSubmission.Artifact.artifact.instructionPC 2874 = 3718 := by
  rw [show (2874:Nat)=2683+(2874-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3955 : CycleSubmission.Artifact.artifact.instructionPC 2875 = 3721 := by
  rw [show (2875:Nat)=2683+(2875-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3956 : CycleSubmission.Artifact.artifact.instructionPC 2876 = 3724 := by
  rw [show (2876:Nat)=2683+(2876-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3957 : CycleSubmission.Artifact.artifact.instructionPC 2877 = 3725 := by
  rw [show (2877:Nat)=2683+(2877-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4190 : CycleSubmission.Artifact.artifact.instructionPC 2705 = 3477 := by
  rw [show (2705:Nat)=2683+(2705-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4193 : CycleSubmission.Artifact.artifact.instructionPC 2706 = 3478 := by
  rw [show (2706:Nat)=2683+(2706-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4194 : CycleSubmission.Artifact.artifact.instructionPC 2707 = 3481 := by
  rw [show (2707:Nat)=2683+(2707-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4547 : CycleSubmission.Artifact.artifact.instructionPC 2878 = 3726 := by
  rw [show (2878:Nat)=2683+(2878-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4548 : CycleSubmission.Artifact.artifact.instructionPC 2879 = 3727 := by
  rw [show (2879:Nat)=2683+(2879-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC3999 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3454 := by
  rw [show (2691:Nat)=2683+(2691-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3462 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3462 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2695 (by rfl)

@[simp] theorem fixedPC4000 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3457 := by
  rw [show (2692:Nat)=2683+(2692-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4001 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3458 := by
  rw [show (2693:Nat)=2683+(2693-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4002 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3461 := by
  rw [show (2694:Nat)=2683+(2694-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4003 : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3462 := by
  rw [show (2695:Nat)=2683+(2695-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4004 : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3463 := by
  rw [show (2696:Nat)=2683+(2696-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4005 : CycleSubmission.Artifact.artifact.instructionPC 2697 = 3466 := by
  rw [show (2697:Nat)=2683+(2697-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4006 : CycleSubmission.Artifact.artifact.instructionPC 2698 = 3467 := by
  rw [show (2698:Nat)=2683+(2698-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4007 : CycleSubmission.Artifact.artifact.instructionPC 2699 = 3469 := by
  rw [show (2699:Nat)=2683+(2699-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4008 : CycleSubmission.Artifact.artifact.instructionPC 2700 = 3470 := by
  rw [show (2700:Nat)=2683+(2700-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4009 : CycleSubmission.Artifact.artifact.instructionPC 2701 = 3471 := by
  rw [show (2701:Nat)=2683+(2701-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4010 : CycleSubmission.Artifact.artifact.instructionPC 2702 = 3472 := by
  rw [show (2702:Nat)=2683+(2702-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4011 : CycleSubmission.Artifact.artifact.instructionPC 2703 = 3473 := by
  rw [show (2703:Nat)=2683+(2703-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4012 : CycleSubmission.Artifact.artifact.instructionPC 2704 = 3476 := by
  rw [show (2704:Nat)=2683+(2704-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2883 : CycleSubmission.Artifact.artifact.instructionPC 2679 = 3438 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : CycleSubmission.Artifact.artifact.instructionPC 2680 = 3439 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : CycleSubmission.Artifact.artifact.instructionPC 2681 = 3440 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : CycleSubmission.Artifact.artifact.instructionPC 2682 = 3441 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3442 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3443 := by
  rw [show (2684:Nat)=2683+(2684-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2890 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3444 := by
  rw [show (2685:Nat)=2683+(2685-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2891 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3447 := by
  rw [show (2686:Nat)=2683+(2686-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2892 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3448 := by
  rw [show (2687:Nat)=2683+(2687-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2893 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3448 := by
  rw [show (2687:Nat)=2683+(2687-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2894 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3449 := by
  rw [show (2688:Nat)=2683+(2688-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2895 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3452 := by
  rw [show (2689:Nat)=2683+(2689-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2896 : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3453 := by
  rw [show (2690:Nat)=2683+(2690-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2930 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3454 := by
  rw [show (2691:Nat)=2683+(2691-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2931 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3457 := by
  rw [show (2692:Nat)=2683+(2692-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2932 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3458 := by
  rw [show (2693:Nat)=2683+(2693-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2933 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3461 := by
  rw [show (2694:Nat)=2683+(2694-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2934 : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3462 := by
  rw [show (2695:Nat)=2683+(2695-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2935 : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3463 := by
  rw [show (2696:Nat)=2683+(2696-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2936 : CycleSubmission.Artifact.artifact.instructionPC 2697 = 3466 := by
  rw [show (2697:Nat)=2683+(2697-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2937 : CycleSubmission.Artifact.artifact.instructionPC 2698 = 3467 := by
  rw [show (2698:Nat)=2683+(2698-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2938 : CycleSubmission.Artifact.artifact.instructionPC 2699 = 3469 := by
  rw [show (2699:Nat)=2683+(2699-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2939 : CycleSubmission.Artifact.artifact.instructionPC 2700 = 3470 := by
  rw [show (2700:Nat)=2683+(2700-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2940 : CycleSubmission.Artifact.artifact.instructionPC 2701 = 3471 := by
  rw [show (2701:Nat)=2683+(2701-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2941 : CycleSubmission.Artifact.artifact.instructionPC 2702 = 3472 := by
  rw [show (2702:Nat)=2683+(2702-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2942 : CycleSubmission.Artifact.artifact.instructionPC 2703 = 3473 := by
  rw [show (2703:Nat)=2683+(2703-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2943 : CycleSubmission.Artifact.artifact.instructionPC 2704 = 3476 := by
  rw [show (2704:Nat)=2683+(2704-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3698 := by
  rw [show (2862:Nat)=2683+(2862-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3701 := by
  rw [show (2863:Nat)=2683+(2863-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3702 := by
  rw [show (2864:Nat)=2683+(2864-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3705 := by
  rw [show (2865:Nat)=2683+(2865-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3706 := by
  rw [show (2866:Nat)=2683+(2866-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2867 = 3707 := by
  rw [show (2867:Nat)=2683+(2867-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2868 = 3710 := by
  rw [show (2868:Nat)=2683+(2868-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3713 := by
  rw [show (2869:Nat)=2683+(2869-2683) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

end CycleSubmission.Global.Fast
