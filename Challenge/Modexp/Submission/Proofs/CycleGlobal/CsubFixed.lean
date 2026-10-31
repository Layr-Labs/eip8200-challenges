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
  [pushAt 2722 2 2688,
   opAt 2723 .MLOAD,
   pushAt 2724 1 128,
   opAt 2725 .EQ,
   pushAt 2726 2 3462,
   opAt 2727 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2722 2 2688,
   opAt 2723 .MLOAD,
   pushAt 2724 1 128,
   opAt 2725 .EQ,
   pushAt 2726 2 3462,
   opAt 2727 .JUMPI,
   opAt 2690 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2728 .JUMPDEST,
   pushAt 2729 2 2336,
   opAt 2730 .MLOAD,
   pushAt 2731 1 224,
   opAt 2732 .MLOAD,
   opAt 2733 (.Dup ⟨0, by decide⟩),
   opAt 2734 (.Dup ⟨2, by decide⟩),
   opAt 2735 .SUB,
   pushAt 2736 2 2016,
   opAt 2737 .MSTORE,
   opAt 2738 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2739 (.Dup ⟨0, by decide⟩),
   pushAt 2740 1 192,
   opAt 2741 .MLOAD,
   opAt 2742 .ADD,
   opAt 2743 (.Dup ⟨0, by decide⟩),
   pushAt 2744 2 2304,
   opAt 2745 .MLOAD,
   opAt 2746 (.Dup ⟨1, by decide⟩),
   opAt 2747 (.Dup ⟨1, by decide⟩),
   opAt 2748 .SUB,
   pushAt 2749 2 1984,
   opAt 2750 .MSTORE,
   opAt 2751 .LT,
   opAt 2752 (.Swap ⟨1, by decide⟩),
   opAt 2753 .GT,
   opAt 2754 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2755 (.Dup ⟨0, by decide⟩),
   pushAt 2756 1 160,
   opAt 2757 .MLOAD,
   opAt 2758 .ADD,
   opAt 2759 (.Dup ⟨0, by decide⟩),
   pushAt 2760 2 2272,
   opAt 2761 .MLOAD,
   opAt 2762 (.Dup ⟨1, by decide⟩),
   opAt 2763 (.Dup ⟨1, by decide⟩),
   opAt 2764 .SUB,
   pushAt 2765 2 1952,
   opAt 2766 .MSTORE,
   opAt 2767 .LT,
   opAt 2768 (.Swap ⟨1, by decide⟩),
   opAt 2769 .GT,
   opAt 2770 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2771 (.Dup ⟨0, by decide⟩),
   pushAt 2772 1 128,
   opAt 2773 .MLOAD,
   opAt 2774 .ADD,
   opAt 2775 (.Dup ⟨0, by decide⟩),
   pushAt 2776 2 2240,
   opAt 2777 .MLOAD,
   opAt 2778 (.Dup ⟨1, by decide⟩),
   opAt 2779 (.Dup ⟨1, by decide⟩),
   opAt 2780 .SUB,
   pushAt 2781 2 1920,
   opAt 2782 .MSTORE,
   opAt 2783 .LT,
   opAt 2784 (.Swap ⟨1, by decide⟩),
   opAt 2785 .GT,
   opAt 2786 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2787 (.Dup ⟨0, by decide⟩),
   pushAt 2788 1 96,
   opAt 2789 .MLOAD,
   opAt 2790 .ADD,
   opAt 2791 (.Dup ⟨0, by decide⟩),
   pushAt 2792 2 2208,
   opAt 2793 .MLOAD,
   opAt 2794 (.Dup ⟨1, by decide⟩),
   opAt 2795 (.Dup ⟨1, by decide⟩),
   opAt 2796 .SUB,
   pushAt 2797 2 1888,
   opAt 2798 .MSTORE,
   opAt 2799 .LT,
   opAt 2800 (.Swap ⟨1, by decide⟩),
   opAt 2801 .GT,
   opAt 2802 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2803 .JUMPDEST,
   opAt 2804 (.Dup ⟨0, by decide⟩),
   pushAt 2805 1 64,
   opAt 2806 .MLOAD,
   opAt 2807 .ADD,
   opAt 2808 (.Dup ⟨0, by decide⟩),
   pushAt 2809 2 2176,
   opAt 2810 .MLOAD,
   opAt 2811 (.Dup ⟨1, by decide⟩),
   opAt 2812 (.Dup ⟨1, by decide⟩),
   opAt 2813 .SUB,
   pushAt 2814 2 1856,
   opAt 2815 .MSTORE,
   opAt 2816 .LT,
   opAt 2817 (.Swap ⟨1, by decide⟩),
   opAt 2818 .GT,
   opAt 2819 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2820 (.Dup ⟨0, by decide⟩),
   pushAt 2821 1 32,
   opAt 2822 .MLOAD,
   opAt 2823 .ADD,
   opAt 2824 (.Dup ⟨0, by decide⟩),
   pushAt 2825 2 2144,
   opAt 2826 .MLOAD,
   opAt 2827 (.Dup ⟨1, by decide⟩),
   opAt 2828 (.Dup ⟨1, by decide⟩),
   opAt 2829 .SUB,
   pushAt 2830 2 1824,
   opAt 2831 .MSTORE,
   opAt 2832 .LT,
   opAt 2833 (.Swap ⟨1, by decide⟩),
   opAt 2834 .GT,
   opAt 2835 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2836 (.Dup ⟨0, by decide⟩),
   pushAt 2837 0 0,
   opAt 2838 .MLOAD,
   opAt 2839 .ADD,
   opAt 2840 (.Dup ⟨0, by decide⟩),
   pushAt 2841 2 2112,
   opAt 2842 .MLOAD,
   opAt 2843 (.Dup ⟨1, by decide⟩),
   opAt 2844 (.Dup ⟨1, by decide⟩),
   opAt 2845 .SUB,
   pushAt 2846 2 1792,
   opAt 2847 .MSTORE,
   opAt 2848 .LT,
   opAt 2849 (.Swap ⟨1, by decide⟩),
   opAt 2850 .GT,
   opAt 2851 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2852 .ISZERO,
   pushAt 2853 2 2080,
   opAt 2854 .MLOAD,
   opAt 2855 .OR,
   pushAt 2856 2 3717,
   opAt 2857 .JUMPI,
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
  [opAt 2852 .ISZERO,
   pushAt 2853 2 2080,
   opAt 2854 .MLOAD,
   opAt 2855 .OR,
   pushAt 2856 2 3717,
   opAt 2857 .JUMPI,
   pushAt 2858 2 3706,
   opAt 2859 .JUMP,
   opAt 2865 .JUMPDEST,
   pushAt 2866 2 2112,
   pushAt 2867 2 2688,
   opAt 2868 .MLOAD,
   opAt 2869 (.Swap ⟨1, by decide⟩),
   opAt 2870 .MCOPY,
   opAt 2871 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2691 2 2208,
   opAt 2692 .MLOAD,
   pushAt 2693 1 96,
   opAt 2694 .MLOAD,
   opAt 2695 (.Dup ⟨0, by decide⟩),
   opAt 2696 (.Dup ⟨2, by decide⟩),
   opAt 2697 .SUB,
   pushAt 2698 2 1888,
   opAt 2699 .MSTORE,
   opAt 2700 .GT,
   pushAt 2701 2 3620,
   opAt 2702 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2803 .JUMPDEST,
   opAt 2804 (.Dup ⟨0, by decide⟩),
   pushAt 2805 1 64,
   opAt 2806 .MLOAD,
   opAt 2807 .ADD,
   opAt 2808 (.Dup ⟨0, by decide⟩),
   pushAt 2809 2 2176,
   opAt 2810 .MLOAD,
   opAt 2811 (.Dup ⟨1, by decide⟩),
   opAt 2812 (.Dup ⟨1, by decide⟩),
   opAt 2813 .SUB,
   pushAt 2814 2 1856,
   opAt 2815 .MSTORE,
   opAt 2816 .LT,
   opAt 2817 (.Swap ⟨1, by decide⟩),
   opAt 2818 .GT,
   opAt 2819 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2820 (.Dup ⟨0, by decide⟩),
   pushAt 2821 1 32,
   opAt 2822 .MLOAD,
   opAt 2823 .ADD,
   opAt 2824 (.Dup ⟨0, by decide⟩),
   pushAt 2825 2 2144,
   opAt 2826 .MLOAD,
   opAt 2827 (.Dup ⟨1, by decide⟩),
   opAt 2828 (.Dup ⟨1, by decide⟩),
   opAt 2829 .SUB,
   pushAt 2830 2 1824,
   opAt 2831 .MSTORE,
   opAt 2832 .LT,
   opAt 2833 (.Swap ⟨1, by decide⟩),
   opAt 2834 .GT,
   opAt 2835 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2836 (.Dup ⟨0, by decide⟩),
   pushAt 2837 0 0,
   opAt 2838 .MLOAD,
   opAt 2839 .ADD,
   opAt 2840 (.Dup ⟨0, by decide⟩),
   pushAt 2841 2 2112,
   opAt 2842 .MLOAD,
   opAt 2843 (.Dup ⟨1, by decide⟩),
   opAt 2844 (.Dup ⟨1, by decide⟩),
   opAt 2845 .SUB,
   pushAt 2846 2 1792,
   opAt 2847 .MSTORE,
   opAt 2848 .LT,
   opAt 2849 (.Swap ⟨1, by decide⟩),
   opAt 2850 .GT,
   opAt 2851 .OR]

private theorem cycleAnchor : CycleSubmission.Artifact.artifact.instructionPC 2675 = 3447 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem fixedPC3777 : CycleSubmission.Artifact.artifact.instructionPC 2717 = 3500 := by
  rw [show (2717:Nat)=2675+(2717-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3778 : CycleSubmission.Artifact.artifact.instructionPC 2858 = 3693 := by
  rw [show (2858:Nat)=2675+(2858-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3779 : CycleSubmission.Artifact.artifact.instructionPC 2859 = 3696 := by
  rw [show (2859:Nat)=2675+(2859-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3787 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3697 := by
  rw [show (2860:Nat)=2675+(2860-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3788 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3702 := by
  rw [show (2861:Nat)=2675+(2861-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3789 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3703 := by
  rw [show (2862:Nat)=2675+(2862-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3790 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3704 := by
  rw [show (2863:Nat)=2675+(2863-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3791 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3705 := by
  rw [show (2864:Nat)=2675+(2864-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3792 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3706 := by
  rw [show (2865:Nat)=2675+(2865-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3793 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3707 := by
  rw [show (2866:Nat)=2675+(2866-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3794 : CycleSubmission.Artifact.artifact.instructionPC 2867 = 3710 := by
  rw [show (2867:Nat)=2675+(2867-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3795 : CycleSubmission.Artifact.artifact.instructionPC 2868 = 3713 := by
  rw [show (2868:Nat)=2675+(2868-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3796 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3714 := by
  rw [show (2869:Nat)=2675+(2869-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3797 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3715 := by
  rw [show (2870:Nat)=2675+(2870-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3798 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3715 := fixedPC3797

@[simp] theorem fixedPC3799 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3715 := fixedPC3797

@[simp] theorem fixedPC3800 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3716 := by
  rw [show (2871:Nat)=2675+(2871-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3801 : CycleSubmission.Artifact.artifact.instructionPC 2872 = 3717 := by
  rw [show (2872:Nat)=2675+(2872-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3802 : CycleSubmission.Artifact.artifact.instructionPC 2873 = 3718 := by
  rw [show (2873:Nat)=2675+(2873-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3803 : CycleSubmission.Artifact.artifact.instructionPC 2874 = 3721 := by
  rw [show (2874:Nat)=2675+(2874-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3804 : CycleSubmission.Artifact.artifact.instructionPC 2875 = 3724 := by
  rw [show (2875:Nat)=2675+(2875-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : CycleSubmission.Artifact.artifact.instructionPC 2718 = 3501 := by
  rw [show (2718:Nat)=2675+(2718-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3115 : CycleSubmission.Artifact.artifact.instructionPC 2719 = 3502 := by
  rw [show (2719:Nat)=2675+(2719-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3116 : CycleSubmission.Artifact.artifact.instructionPC 2720 = 3503 := by
  rw [show (2720:Nat)=2675+(2720-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3117 : CycleSubmission.Artifact.artifact.instructionPC 2721 = 3506 := by
  rw [show (2721:Nat)=2675+(2721-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3118 : CycleSubmission.Artifact.artifact.instructionPC 2722 = 3509 := by
  rw [show (2722:Nat)=2675+(2722-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3119 : CycleSubmission.Artifact.artifact.instructionPC 2723 = 3512 := by
  rw [show (2723:Nat)=2675+(2723-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3458 := by
  rw [show (2686:Nat)=2675+(2686-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3462 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3462 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2690 (by rfl)

@[simp] theorem fixedPC3805 : CycleSubmission.Artifact.artifact.instructionPC 2724 = 3513 := by
  rw [show (2724:Nat)=2675+(2724-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3806 : CycleSubmission.Artifact.artifact.instructionPC 2725 = 3515 := by
  rw [show (2725:Nat)=2675+(2725-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3807 : CycleSubmission.Artifact.artifact.instructionPC 2726 = 3516 := by
  rw [show (2726:Nat)=2675+(2726-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3808 : CycleSubmission.Artifact.artifact.instructionPC 2727 = 3519 := by
  rw [show (2727:Nat)=2675+(2727-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPCs8 : CycleSubmission.Artifact.artifact.instructionPC 2728 = 3520 := by
  rw [show (2728:Nat)=2675+(2728-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3809 : CycleSubmission.Artifact.artifact.instructionPC 2729 = 3521 := by
  rw [show (2729:Nat)=2675+(2729-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3810 : CycleSubmission.Artifact.artifact.instructionPC 2730 = 3524 := by
  rw [show (2730:Nat)=2675+(2730-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3811 : CycleSubmission.Artifact.artifact.instructionPC 2731 = 3525 := by
  rw [show (2731:Nat)=2675+(2731-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3812 : CycleSubmission.Artifact.artifact.instructionPC 2732 = 3527 := by
  rw [show (2732:Nat)=2675+(2732-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3813 : CycleSubmission.Artifact.artifact.instructionPC 2733 = 3528 := by
  rw [show (2733:Nat)=2675+(2733-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3814 : CycleSubmission.Artifact.artifact.instructionPC 2734 = 3529 := by
  rw [show (2734:Nat)=2675+(2734-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3815 : CycleSubmission.Artifact.artifact.instructionPC 2735 = 3530 := by
  rw [show (2735:Nat)=2675+(2735-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3816 : CycleSubmission.Artifact.artifact.instructionPC 2735 = 3530 := by
  rw [show (2735:Nat)=2675+(2735-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3817 : CycleSubmission.Artifact.artifact.instructionPC 2736 = 3531 := by
  rw [show (2736:Nat)=2675+(2736-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3818 : CycleSubmission.Artifact.artifact.instructionPC 2737 = 3534 := by
  rw [show (2737:Nat)=2675+(2737-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3819 : CycleSubmission.Artifact.artifact.instructionPC 2738 = 3535 := by
  rw [show (2738:Nat)=2675+(2738-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3820 : CycleSubmission.Artifact.artifact.instructionPC 2739 = 3536 := by
  rw [show (2739:Nat)=2675+(2739-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3821 : CycleSubmission.Artifact.artifact.instructionPC 2740 = 3537 := by
  rw [show (2740:Nat)=2675+(2740-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3822 : CycleSubmission.Artifact.artifact.instructionPC 2741 = 3539 := by
  rw [show (2741:Nat)=2675+(2741-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3823 : CycleSubmission.Artifact.artifact.instructionPC 2742 = 3540 := by
  rw [show (2742:Nat)=2675+(2742-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3824 : CycleSubmission.Artifact.artifact.instructionPC 2743 = 3541 := by
  rw [show (2743:Nat)=2675+(2743-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3825 : CycleSubmission.Artifact.artifact.instructionPC 2744 = 3542 := by
  rw [show (2744:Nat)=2675+(2744-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3826 : CycleSubmission.Artifact.artifact.instructionPC 2745 = 3545 := by
  rw [show (2745:Nat)=2675+(2745-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3827 : CycleSubmission.Artifact.artifact.instructionPC 2746 = 3546 := by
  rw [show (2746:Nat)=2675+(2746-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3828 : CycleSubmission.Artifact.artifact.instructionPC 2747 = 3547 := by
  rw [show (2747:Nat)=2675+(2747-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3829 : CycleSubmission.Artifact.artifact.instructionPC 2748 = 3548 := by
  rw [show (2748:Nat)=2675+(2748-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3830 : CycleSubmission.Artifact.artifact.instructionPC 2749 = 3549 := by
  rw [show (2749:Nat)=2675+(2749-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3831 : CycleSubmission.Artifact.artifact.instructionPC 2750 = 3552 := by
  rw [show (2750:Nat)=2675+(2750-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3832 : CycleSubmission.Artifact.artifact.instructionPC 2751 = 3553 := by
  rw [show (2751:Nat)=2675+(2751-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3833 : CycleSubmission.Artifact.artifact.instructionPC 2752 = 3554 := by
  rw [show (2752:Nat)=2675+(2752-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3834 : CycleSubmission.Artifact.artifact.instructionPC 2752 = 3554 := by
  rw [show (2752:Nat)=2675+(2752-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3835 : CycleSubmission.Artifact.artifact.instructionPC 2753 = 3555 := by
  rw [show (2753:Nat)=2675+(2753-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3836 : CycleSubmission.Artifact.artifact.instructionPC 2754 = 3556 := by
  rw [show (2754:Nat)=2675+(2754-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3837 : CycleSubmission.Artifact.artifact.instructionPC 2755 = 3557 := by
  rw [show (2755:Nat)=2675+(2755-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3838 : CycleSubmission.Artifact.artifact.instructionPC 2756 = 3558 := by
  rw [show (2756:Nat)=2675+(2756-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3839 : CycleSubmission.Artifact.artifact.instructionPC 2757 = 3560 := by
  rw [show (2757:Nat)=2675+(2757-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3840 : CycleSubmission.Artifact.artifact.instructionPC 2758 = 3561 := by
  rw [show (2758:Nat)=2675+(2758-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3841 : CycleSubmission.Artifact.artifact.instructionPC 2759 = 3562 := by
  rw [show (2759:Nat)=2675+(2759-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3842 : CycleSubmission.Artifact.artifact.instructionPC 2760 = 3563 := by
  rw [show (2760:Nat)=2675+(2760-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3843 : CycleSubmission.Artifact.artifact.instructionPC 2761 = 3566 := by
  rw [show (2761:Nat)=2675+(2761-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3844 : CycleSubmission.Artifact.artifact.instructionPC 2762 = 3567 := by
  rw [show (2762:Nat)=2675+(2762-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3845 : CycleSubmission.Artifact.artifact.instructionPC 2763 = 3568 := by
  rw [show (2763:Nat)=2675+(2763-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3846 : CycleSubmission.Artifact.artifact.instructionPC 2764 = 3569 := by
  rw [show (2764:Nat)=2675+(2764-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3847 : CycleSubmission.Artifact.artifact.instructionPC 2765 = 3570 := by
  rw [show (2765:Nat)=2675+(2765-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3848 : CycleSubmission.Artifact.artifact.instructionPC 2766 = 3573 := by
  rw [show (2766:Nat)=2675+(2766-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3849 : CycleSubmission.Artifact.artifact.instructionPC 2767 = 3574 := by
  rw [show (2767:Nat)=2675+(2767-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3850 : CycleSubmission.Artifact.artifact.instructionPC 2768 = 3575 := by
  rw [show (2768:Nat)=2675+(2768-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3851 : CycleSubmission.Artifact.artifact.instructionPC 2769 = 3576 := by
  rw [show (2769:Nat)=2675+(2769-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3852 : CycleSubmission.Artifact.artifact.instructionPC 2769 = 3576 := by
  rw [show (2769:Nat)=2675+(2769-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3853 : CycleSubmission.Artifact.artifact.instructionPC 2770 = 3577 := by
  rw [show (2770:Nat)=2675+(2770-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3854 : CycleSubmission.Artifact.artifact.instructionPC 2771 = 3578 := by
  rw [show (2771:Nat)=2675+(2771-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3855 : CycleSubmission.Artifact.artifact.instructionPC 2772 = 3579 := by
  rw [show (2772:Nat)=2675+(2772-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3856 : CycleSubmission.Artifact.artifact.instructionPC 2773 = 3581 := by
  rw [show (2773:Nat)=2675+(2773-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3857 : CycleSubmission.Artifact.artifact.instructionPC 2774 = 3582 := by
  rw [show (2774:Nat)=2675+(2774-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3858 : CycleSubmission.Artifact.artifact.instructionPC 2775 = 3583 := by
  rw [show (2775:Nat)=2675+(2775-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3859 : CycleSubmission.Artifact.artifact.instructionPC 2776 = 3584 := by
  rw [show (2776:Nat)=2675+(2776-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3860 : CycleSubmission.Artifact.artifact.instructionPC 2777 = 3587 := by
  rw [show (2777:Nat)=2675+(2777-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3861 : CycleSubmission.Artifact.artifact.instructionPC 2778 = 3588 := by
  rw [show (2778:Nat)=2675+(2778-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3862 : CycleSubmission.Artifact.artifact.instructionPC 2779 = 3589 := by
  rw [show (2779:Nat)=2675+(2779-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3863 : CycleSubmission.Artifact.artifact.instructionPC 2780 = 3590 := by
  rw [show (2780:Nat)=2675+(2780-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3864 : CycleSubmission.Artifact.artifact.instructionPC 2781 = 3591 := by
  rw [show (2781:Nat)=2675+(2781-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3865 : CycleSubmission.Artifact.artifact.instructionPC 2782 = 3594 := by
  rw [show (2782:Nat)=2675+(2782-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3866 : CycleSubmission.Artifact.artifact.instructionPC 2783 = 3595 := by
  rw [show (2783:Nat)=2675+(2783-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3867 : CycleSubmission.Artifact.artifact.instructionPC 2784 = 3596 := by
  rw [show (2784:Nat)=2675+(2784-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3868 : CycleSubmission.Artifact.artifact.instructionPC 2785 = 3597 := by
  rw [show (2785:Nat)=2675+(2785-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3869 : CycleSubmission.Artifact.artifact.instructionPC 2786 = 3598 := by
  rw [show (2786:Nat)=2675+(2786-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3871 : CycleSubmission.Artifact.artifact.instructionPC 2786 = 3598 := by
  rw [show (2786:Nat)=2675+(2786-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3872 : CycleSubmission.Artifact.artifact.instructionPC 2787 = 3599 := by
  rw [show (2787:Nat)=2675+(2787-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3873 : CycleSubmission.Artifact.artifact.instructionPC 2788 = 3600 := by
  rw [show (2788:Nat)=2675+(2788-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3874 : CycleSubmission.Artifact.artifact.instructionPC 2789 = 3602 := by
  rw [show (2789:Nat)=2675+(2789-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3875 : CycleSubmission.Artifact.artifact.instructionPC 2790 = 3603 := by
  rw [show (2790:Nat)=2675+(2790-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3876 : CycleSubmission.Artifact.artifact.instructionPC 2791 = 3604 := by
  rw [show (2791:Nat)=2675+(2791-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3877 : CycleSubmission.Artifact.artifact.instructionPC 2792 = 3605 := by
  rw [show (2792:Nat)=2675+(2792-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3878 : CycleSubmission.Artifact.artifact.instructionPC 2793 = 3608 := by
  rw [show (2793:Nat)=2675+(2793-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3879 : CycleSubmission.Artifact.artifact.instructionPC 2794 = 3609 := by
  rw [show (2794:Nat)=2675+(2794-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3880 : CycleSubmission.Artifact.artifact.instructionPC 2795 = 3610 := by
  rw [show (2795:Nat)=2675+(2795-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3881 : CycleSubmission.Artifact.artifact.instructionPC 2796 = 3611 := by
  rw [show (2796:Nat)=2675+(2796-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3882 : CycleSubmission.Artifact.artifact.instructionPC 2797 = 3612 := by
  rw [show (2797:Nat)=2675+(2797-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3883 : CycleSubmission.Artifact.artifact.instructionPC 2798 = 3615 := by
  rw [show (2798:Nat)=2675+(2798-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3884 : CycleSubmission.Artifact.artifact.instructionPC 2799 = 3616 := by
  rw [show (2799:Nat)=2675+(2799-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3885 : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3617 := by
  rw [show (2800:Nat)=2675+(2800-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3886 : CycleSubmission.Artifact.artifact.instructionPC 2801 = 3618 := by
  rw [show (2801:Nat)=2675+(2801-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3887 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3619 := by
  rw [show (2802:Nat)=2675+(2802-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3888 : CycleSubmission.Artifact.artifact.instructionPC 2803 = 3620 := by
  rw [show (2803:Nat)=2675+(2803-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3889 : CycleSubmission.Artifact.artifact.instructionPC 2803 = 3620 := by
  rw [show (2803:Nat)=2675+(2803-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3620 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2803 = 3620 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2803 (by rfl)

@[simp] theorem fixedPC3890 : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3621 := by
  rw [show (2804:Nat)=2675+(2804-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3891 : CycleSubmission.Artifact.artifact.instructionPC 2805 = 3622 := by
  rw [show (2805:Nat)=2675+(2805-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3892 : CycleSubmission.Artifact.artifact.instructionPC 2806 = 3624 := by
  rw [show (2806:Nat)=2675+(2806-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3893 : CycleSubmission.Artifact.artifact.instructionPC 2807 = 3625 := by
  rw [show (2807:Nat)=2675+(2807-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3894 : CycleSubmission.Artifact.artifact.instructionPC 2808 = 3626 := by
  rw [show (2808:Nat)=2675+(2808-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3895 : CycleSubmission.Artifact.artifact.instructionPC 2809 = 3627 := by
  rw [show (2809:Nat)=2675+(2809-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3896 : CycleSubmission.Artifact.artifact.instructionPC 2810 = 3630 := by
  rw [show (2810:Nat)=2675+(2810-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3897 : CycleSubmission.Artifact.artifact.instructionPC 2811 = 3631 := by
  rw [show (2811:Nat)=2675+(2811-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3898 : CycleSubmission.Artifact.artifact.instructionPC 2812 = 3632 := by
  rw [show (2812:Nat)=2675+(2812-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3899 : CycleSubmission.Artifact.artifact.instructionPC 2813 = 3633 := by
  rw [show (2813:Nat)=2675+(2813-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3900 : CycleSubmission.Artifact.artifact.instructionPC 2814 = 3634 := by
  rw [show (2814:Nat)=2675+(2814-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3901 : CycleSubmission.Artifact.artifact.instructionPC 2815 = 3637 := by
  rw [show (2815:Nat)=2675+(2815-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3902 : CycleSubmission.Artifact.artifact.instructionPC 2816 = 3638 := by
  rw [show (2816:Nat)=2675+(2816-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3903 : CycleSubmission.Artifact.artifact.instructionPC 2817 = 3639 := by
  rw [show (2817:Nat)=2675+(2817-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3904 : CycleSubmission.Artifact.artifact.instructionPC 2818 = 3640 := by
  rw [show (2818:Nat)=2675+(2818-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3905 : CycleSubmission.Artifact.artifact.instructionPC 2819 = 3641 := by
  rw [show (2819:Nat)=2675+(2819-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3906 : CycleSubmission.Artifact.artifact.instructionPC 2820 = 3642 := by
  rw [show (2820:Nat)=2675+(2820-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3907 : CycleSubmission.Artifact.artifact.instructionPC 2821 = 3643 := by
  rw [show (2821:Nat)=2675+(2821-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3908 : CycleSubmission.Artifact.artifact.instructionPC 2821 = 3643 := by
  rw [show (2821:Nat)=2675+(2821-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3909 : CycleSubmission.Artifact.artifact.instructionPC 2822 = 3645 := by
  rw [show (2822:Nat)=2675+(2822-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3910 : CycleSubmission.Artifact.artifact.instructionPC 2823 = 3646 := by
  rw [show (2823:Nat)=2675+(2823-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3911 : CycleSubmission.Artifact.artifact.instructionPC 2824 = 3647 := by
  rw [show (2824:Nat)=2675+(2824-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3912 : CycleSubmission.Artifact.artifact.instructionPC 2825 = 3648 := by
  rw [show (2825:Nat)=2675+(2825-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3913 : CycleSubmission.Artifact.artifact.instructionPC 2826 = 3651 := by
  rw [show (2826:Nat)=2675+(2826-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3914 : CycleSubmission.Artifact.artifact.instructionPC 2827 = 3652 := by
  rw [show (2827:Nat)=2675+(2827-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3915 : CycleSubmission.Artifact.artifact.instructionPC 2828 = 3653 := by
  rw [show (2828:Nat)=2675+(2828-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3916 : CycleSubmission.Artifact.artifact.instructionPC 2829 = 3654 := by
  rw [show (2829:Nat)=2675+(2829-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3917 : CycleSubmission.Artifact.artifact.instructionPC 2830 = 3655 := by
  rw [show (2830:Nat)=2675+(2830-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3918 : CycleSubmission.Artifact.artifact.instructionPC 2831 = 3658 := by
  rw [show (2831:Nat)=2675+(2831-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3919 : CycleSubmission.Artifact.artifact.instructionPC 2832 = 3659 := by
  rw [show (2832:Nat)=2675+(2832-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3920 : CycleSubmission.Artifact.artifact.instructionPC 2833 = 3660 := by
  rw [show (2833:Nat)=2675+(2833-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2834 = 3661 := by
  rw [show (2834:Nat)=2675+(2834-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2835 = 3662 := by
  rw [show (2835:Nat)=2675+(2835-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2836 = 3663 := by
  rw [show (2836:Nat)=2675+(2836-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2837 = 3664 := by
  rw [show (2837:Nat)=2675+(2837-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2838 = 3665 := by
  rw [show (2838:Nat)=2675+(2838-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2838 = 3665 := by
  rw [show (2838:Nat)=2675+(2838-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2839 = 3666 := by
  rw [show (2839:Nat)=2675+(2839-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2840 = 3667 := by
  rw [show (2840:Nat)=2675+(2840-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3929 : CycleSubmission.Artifact.artifact.instructionPC 2841 = 3668 := by
  rw [show (2841:Nat)=2675+(2841-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3930 : CycleSubmission.Artifact.artifact.instructionPC 2842 = 3671 := by
  rw [show (2842:Nat)=2675+(2842-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3931 : CycleSubmission.Artifact.artifact.instructionPC 2843 = 3672 := by
  rw [show (2843:Nat)=2675+(2843-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3932 : CycleSubmission.Artifact.artifact.instructionPC 2844 = 3673 := by
  rw [show (2844:Nat)=2675+(2844-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3933 : CycleSubmission.Artifact.artifact.instructionPC 2845 = 3674 := by
  rw [show (2845:Nat)=2675+(2845-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3934 : CycleSubmission.Artifact.artifact.instructionPC 2846 = 3675 := by
  rw [show (2846:Nat)=2675+(2846-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3935 : CycleSubmission.Artifact.artifact.instructionPC 2847 = 3678 := by
  rw [show (2847:Nat)=2675+(2847-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3936 : CycleSubmission.Artifact.artifact.instructionPC 2848 = 3679 := by
  rw [show (2848:Nat)=2675+(2848-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3937 : CycleSubmission.Artifact.artifact.instructionPC 2849 = 3680 := by
  rw [show (2849:Nat)=2675+(2849-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3938 : CycleSubmission.Artifact.artifact.instructionPC 2850 = 3681 := by
  rw [show (2850:Nat)=2675+(2850-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3939 : CycleSubmission.Artifact.artifact.instructionPC 2851 = 3682 := by
  rw [show (2851:Nat)=2675+(2851-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3940 : CycleSubmission.Artifact.artifact.instructionPC 2852 = 3683 := by
  rw [show (2852:Nat)=2675+(2852-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3941 : CycleSubmission.Artifact.artifact.instructionPC 2853 = 3684 := by
  rw [show (2853:Nat)=2675+(2853-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3942 : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3687 := by
  rw [show (2854:Nat)=2675+(2854-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3943 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3688 := by
  rw [show (2855:Nat)=2675+(2855-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3944 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3688 := by
  rw [show (2855:Nat)=2675+(2855-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3945 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3689 := by
  rw [show (2856:Nat)=2675+(2856-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3946 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3692 := by
  rw [show (2857:Nat)=2675+(2857-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3947 : CycleSubmission.Artifact.artifact.instructionPC 2858 = 3693 := by
  rw [show (2858:Nat)=2675+(2858-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3948 : CycleSubmission.Artifact.artifact.instructionPC 2859 = 3696 := by
  rw [show (2859:Nat)=2675+(2859-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3949 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3714 := by
  rw [show (2869:Nat)=2675+(2869-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3950 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3714 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3715 := by
  rw [show (2870:Nat)=2675+(2870-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3952 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3716 := by
  rw [show (2871:Nat)=2675+(2871-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3953 : CycleSubmission.Artifact.artifact.instructionPC 2872 = 3717 := by
  rw [show (2872:Nat)=2675+(2872-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3954 : CycleSubmission.Artifact.artifact.instructionPC 2873 = 3718 := by
  rw [show (2873:Nat)=2675+(2873-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3955 : CycleSubmission.Artifact.artifact.instructionPC 2874 = 3721 := by
  rw [show (2874:Nat)=2675+(2874-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3956 : CycleSubmission.Artifact.artifact.instructionPC 2875 = 3724 := by
  rw [show (2875:Nat)=2675+(2875-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3957 : CycleSubmission.Artifact.artifact.instructionPC 2876 = 3725 := by
  rw [show (2876:Nat)=2675+(2876-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4190 : CycleSubmission.Artifact.artifact.instructionPC 2700 = 3477 := by
  rw [show (2700:Nat)=2675+(2700-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4193 : CycleSubmission.Artifact.artifact.instructionPC 2701 = 3478 := by
  rw [show (2701:Nat)=2675+(2701-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4194 : CycleSubmission.Artifact.artifact.instructionPC 2702 = 3481 := by
  rw [show (2702:Nat)=2675+(2702-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4547 : CycleSubmission.Artifact.artifact.instructionPC 2877 = 3726 := by
  rw [show (2877:Nat)=2675+(2877-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4548 : CycleSubmission.Artifact.artifact.instructionPC 2878 = 3727 := by
  rw [show (2878:Nat)=2675+(2878-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC3999 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3458 := by
  rw [show (2686:Nat)=2675+(2686-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3462 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3462 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2690 (by rfl)

@[simp] theorem fixedPC4000 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3459 := by
  rw [show (2687:Nat)=2675+(2687-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4001 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3460 := by
  rw [show (2688:Nat)=2675+(2688-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4002 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3461 := by
  rw [show (2689:Nat)=2675+(2689-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4003 : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3462 := by
  rw [show (2690:Nat)=2675+(2690-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4004 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3463 := by
  rw [show (2691:Nat)=2675+(2691-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4005 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3466 := by
  rw [show (2692:Nat)=2675+(2692-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4006 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3467 := by
  rw [show (2693:Nat)=2675+(2693-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4007 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3469 := by
  rw [show (2694:Nat)=2675+(2694-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4008 : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3470 := by
  rw [show (2695:Nat)=2675+(2695-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4009 : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3471 := by
  rw [show (2696:Nat)=2675+(2696-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4010 : CycleSubmission.Artifact.artifact.instructionPC 2697 = 3472 := by
  rw [show (2697:Nat)=2675+(2697-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4011 : CycleSubmission.Artifact.artifact.instructionPC 2698 = 3473 := by
  rw [show (2698:Nat)=2675+(2698-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4012 : CycleSubmission.Artifact.artifact.instructionPC 2699 = 3476 := by
  rw [show (2699:Nat)=2675+(2699-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2883 : CycleSubmission.Artifact.artifact.instructionPC 2655 = 3423 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : CycleSubmission.Artifact.artifact.instructionPC 2656 = 3424 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : CycleSubmission.Artifact.artifact.instructionPC 2657 = 3425 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : CycleSubmission.Artifact.artifact.instructionPC 2658 = 3426 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : CycleSubmission.Artifact.artifact.instructionPC 2659 = 3427 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : CycleSubmission.Artifact.artifact.instructionPC 2660 = 3428 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2890 : CycleSubmission.Artifact.artifact.instructionPC 2661 = 3429 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2891 : CycleSubmission.Artifact.artifact.instructionPC 2662 = 3432 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2892 : CycleSubmission.Artifact.artifact.instructionPC 2663 = 3433 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2893 : CycleSubmission.Artifact.artifact.instructionPC 2663 = 3433 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2894 : CycleSubmission.Artifact.artifact.instructionPC 2664 = 3436 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2895 : CycleSubmission.Artifact.artifact.instructionPC 2665 = 3437 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2896 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3457 := by
  rw [show (2685:Nat)=2675+(2685-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2930 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3458 := by
  rw [show (2686:Nat)=2675+(2686-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2931 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3459 := by
  rw [show (2687:Nat)=2675+(2687-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2932 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3460 := by
  rw [show (2688:Nat)=2675+(2688-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2933 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3461 := by
  rw [show (2689:Nat)=2675+(2689-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2934 : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3462 := by
  rw [show (2690:Nat)=2675+(2690-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2935 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3463 := by
  rw [show (2691:Nat)=2675+(2691-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2936 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3466 := by
  rw [show (2692:Nat)=2675+(2692-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2937 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3467 := by
  rw [show (2693:Nat)=2675+(2693-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2938 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3469 := by
  rw [show (2694:Nat)=2675+(2694-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2939 : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3470 := by
  rw [show (2695:Nat)=2675+(2695-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2940 : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3471 := by
  rw [show (2696:Nat)=2675+(2696-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2941 : CycleSubmission.Artifact.artifact.instructionPC 2697 = 3472 := by
  rw [show (2697:Nat)=2675+(2697-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2942 : CycleSubmission.Artifact.artifact.instructionPC 2698 = 3473 := by
  rw [show (2698:Nat)=2675+(2698-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2943 : CycleSubmission.Artifact.artifact.instructionPC 2699 = 3476 := by
  rw [show (2699:Nat)=2675+(2699-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3702 := by
  rw [show (2861:Nat)=2675+(2861-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3703 := by
  rw [show (2862:Nat)=2675+(2862-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3704 := by
  rw [show (2863:Nat)=2675+(2863-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3705 := by
  rw [show (2864:Nat)=2675+(2864-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3706 := by
  rw [show (2865:Nat)=2675+(2865-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3707 := by
  rw [show (2866:Nat)=2675+(2866-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2867 = 3710 := by
  rw [show (2867:Nat)=2675+(2867-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2868 = 3713 := by
  rw [show (2868:Nat)=2675+(2868-2675) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

end CycleSubmission.Global.Fast
