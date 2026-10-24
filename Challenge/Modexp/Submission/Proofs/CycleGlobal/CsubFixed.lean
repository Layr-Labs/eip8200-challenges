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
  [opAt 2723 .JUMPDEST,
   pushAt 2724 2 2688,
   opAt 2725 .MLOAD,
   pushAt 2726 1 128,
   opAt 2727 .EQ,
   pushAt 2728 2 3462,
   opAt 2729 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2723 .JUMPDEST,
   pushAt 2724 2 2688,
   opAt 2725 .MLOAD,
   pushAt 2726 1 128,
   opAt 2727 .EQ,
   pushAt 2728 2 3462,
   opAt 2729 .JUMPI,
   opAt 2696 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2730 .JUMPDEST,
   pushAt 2731 2 2336,
   opAt 2732 .MLOAD,
   pushAt 2733 1 224,
   opAt 2734 .MLOAD,
   opAt 2735 (.Dup ⟨0, by decide⟩),
   opAt 2736 (.Dup ⟨2, by decide⟩),
   opAt 2737 .SUB,
   pushAt 2738 2 2016,
   opAt 2739 .MSTORE,
   opAt 2740 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2741 (.Dup ⟨0, by decide⟩),
   pushAt 2742 1 192,
   opAt 2743 .MLOAD,
   opAt 2744 .ADD,
   opAt 2745 (.Dup ⟨0, by decide⟩),
   pushAt 2746 2 2304,
   opAt 2747 .MLOAD,
   opAt 2748 (.Dup ⟨1, by decide⟩),
   opAt 2749 (.Dup ⟨1, by decide⟩),
   opAt 2750 .SUB,
   pushAt 2751 2 1984,
   opAt 2752 .MSTORE,
   opAt 2753 .LT,
   opAt 2754 (.Swap ⟨1, by decide⟩),
   opAt 2755 .GT,
   opAt 2756 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2757 (.Dup ⟨0, by decide⟩),
   pushAt 2758 1 160,
   opAt 2759 .MLOAD,
   opAt 2760 .ADD,
   opAt 2761 (.Dup ⟨0, by decide⟩),
   pushAt 2762 2 2272,
   opAt 2763 .MLOAD,
   opAt 2764 (.Dup ⟨1, by decide⟩),
   opAt 2765 (.Dup ⟨1, by decide⟩),
   opAt 2766 .SUB,
   pushAt 2767 2 1952,
   opAt 2768 .MSTORE,
   opAt 2769 .LT,
   opAt 2770 (.Swap ⟨1, by decide⟩),
   opAt 2771 .GT,
   opAt 2772 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2773 (.Dup ⟨0, by decide⟩),
   pushAt 2774 1 128,
   opAt 2775 .MLOAD,
   opAt 2776 .ADD,
   opAt 2777 (.Dup ⟨0, by decide⟩),
   pushAt 2778 2 2240,
   opAt 2779 .MLOAD,
   opAt 2780 (.Dup ⟨1, by decide⟩),
   opAt 2781 (.Dup ⟨1, by decide⟩),
   opAt 2782 .SUB,
   pushAt 2783 2 1920,
   opAt 2784 .MSTORE,
   opAt 2785 .LT,
   opAt 2786 (.Swap ⟨1, by decide⟩),
   opAt 2787 .GT,
   opAt 2788 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2789 (.Dup ⟨0, by decide⟩),
   pushAt 2790 1 96,
   opAt 2791 .MLOAD,
   opAt 2792 .ADD,
   opAt 2793 (.Dup ⟨0, by decide⟩),
   pushAt 2794 2 2208,
   opAt 2795 .MLOAD,
   opAt 2796 (.Dup ⟨1, by decide⟩),
   opAt 2797 (.Dup ⟨1, by decide⟩),
   opAt 2798 .SUB,
   pushAt 2799 2 1888,
   opAt 2800 .MSTORE,
   opAt 2801 .LT,
   opAt 2802 (.Swap ⟨1, by decide⟩),
   opAt 2803 .GT,
   opAt 2804 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2805 .JUMPDEST,
   opAt 2806 (.Dup ⟨0, by decide⟩),
   pushAt 2807 1 64,
   opAt 2808 .MLOAD,
   opAt 2809 .ADD,
   opAt 2810 (.Dup ⟨0, by decide⟩),
   pushAt 2811 2 2176,
   opAt 2812 .MLOAD,
   opAt 2813 (.Dup ⟨1, by decide⟩),
   opAt 2814 (.Dup ⟨1, by decide⟩),
   opAt 2815 .SUB,
   pushAt 2816 2 1856,
   opAt 2817 .MSTORE,
   opAt 2818 .LT,
   opAt 2819 (.Swap ⟨1, by decide⟩),
   opAt 2820 .GT,
   opAt 2821 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2822 (.Dup ⟨0, by decide⟩),
   pushAt 2823 1 32,
   opAt 2824 .MLOAD,
   opAt 2825 .ADD,
   opAt 2826 (.Dup ⟨0, by decide⟩),
   pushAt 2827 2 2144,
   opAt 2828 .MLOAD,
   opAt 2829 (.Dup ⟨1, by decide⟩),
   opAt 2830 (.Dup ⟨1, by decide⟩),
   opAt 2831 .SUB,
   pushAt 2832 2 1824,
   opAt 2833 .MSTORE,
   opAt 2834 .LT,
   opAt 2835 (.Swap ⟨1, by decide⟩),
   opAt 2836 .GT,
   opAt 2837 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2838 (.Dup ⟨0, by decide⟩),
   pushAt 2839 0 0,
   opAt 2840 .MLOAD,
   opAt 2841 .ADD,
   opAt 2842 (.Dup ⟨0, by decide⟩),
   pushAt 2843 2 2112,
   opAt 2844 .MLOAD,
   opAt 2845 (.Dup ⟨1, by decide⟩),
   opAt 2846 (.Dup ⟨1, by decide⟩),
   opAt 2847 .SUB,
   pushAt 2848 2 1792,
   opAt 2849 .MSTORE,
   opAt 2850 .LT,
   opAt 2851 (.Swap ⟨1, by decide⟩),
   opAt 2852 .GT,
   opAt 2853 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2854 .ISZERO,
   pushAt 2855 2 2080,
   opAt 2856 .MLOAD,
   opAt 2857 .OR,
   pushAt 2858 2 3717,
   opAt 2859 .JUMPI,
   opAt 2874 .JUMPDEST,
   pushAt 2875 2 1792,
   pushAt 2876 2 2688,
   opAt 2877 .MLOAD,
   opAt 2878 (.Swap ⟨1, by decide⟩),
   opAt 2879 .MCOPY,
   opAt 2880 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2854 .ISZERO,
   pushAt 2855 2 2080,
   opAt 2856 .MLOAD,
   opAt 2857 .OR,
   pushAt 2858 2 3717,
   opAt 2859 .JUMPI,
   pushAt 2860 2 3706,
   opAt 2861 .JUMP,
   opAt 2867 .JUMPDEST,
   pushAt 2868 2 2112,
   pushAt 2869 2 2688,
   opAt 2870 .MLOAD,
   opAt 2871 (.Swap ⟨1, by decide⟩),
   opAt 2872 .MCOPY,
   opAt 2873 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2697 2 2208,
   opAt 2698 .MLOAD,
   pushAt 2699 1 96,
   opAt 2700 .MLOAD,
   opAt 2701 (.Dup ⟨0, by decide⟩),
   opAt 2702 (.Dup ⟨2, by decide⟩),
   opAt 2703 .SUB,
   pushAt 2704 2 1888,
   opAt 2705 .MSTORE,
   opAt 2706 .GT,
   pushAt 2707 2 3620,
   opAt 2708 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2805 .JUMPDEST,
   opAt 2806 (.Dup ⟨0, by decide⟩),
   pushAt 2807 1 64,
   opAt 2808 .MLOAD,
   opAt 2809 .ADD,
   opAt 2810 (.Dup ⟨0, by decide⟩),
   pushAt 2811 2 2176,
   opAt 2812 .MLOAD,
   opAt 2813 (.Dup ⟨1, by decide⟩),
   opAt 2814 (.Dup ⟨1, by decide⟩),
   opAt 2815 .SUB,
   pushAt 2816 2 1856,
   opAt 2817 .MSTORE,
   opAt 2818 .LT,
   opAt 2819 (.Swap ⟨1, by decide⟩),
   opAt 2820 .GT,
   opAt 2821 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2822 (.Dup ⟨0, by decide⟩),
   pushAt 2823 1 32,
   opAt 2824 .MLOAD,
   opAt 2825 .ADD,
   opAt 2826 (.Dup ⟨0, by decide⟩),
   pushAt 2827 2 2144,
   opAt 2828 .MLOAD,
   opAt 2829 (.Dup ⟨1, by decide⟩),
   opAt 2830 (.Dup ⟨1, by decide⟩),
   opAt 2831 .SUB,
   pushAt 2832 2 1824,
   opAt 2833 .MSTORE,
   opAt 2834 .LT,
   opAt 2835 (.Swap ⟨1, by decide⟩),
   opAt 2836 .GT,
   opAt 2837 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2838 (.Dup ⟨0, by decide⟩),
   pushAt 2839 0 0,
   opAt 2840 .MLOAD,
   opAt 2841 .ADD,
   opAt 2842 (.Dup ⟨0, by decide⟩),
   pushAt 2843 2 2112,
   opAt 2844 .MLOAD,
   opAt 2845 (.Dup ⟨1, by decide⟩),
   opAt 2846 (.Dup ⟨1, by decide⟩),
   opAt 2847 .SUB,
   pushAt 2848 2 1792,
   opAt 2849 .MSTORE,
   opAt 2850 .LT,
   opAt 2851 (.Swap ⟨1, by decide⟩),
   opAt 2852 .GT,
   opAt 2853 .OR]

private theorem cycleAnchor : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3442 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem fixedPC3777 : CycleSubmission.Artifact.artifact.instructionPC 2719 = 3500 := by
  rw [show (2719:Nat)=2684+(2719-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3508 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2723 = 3508 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2723 (by rfl)

@[simp] theorem fixedPC3778 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3693 := by
  rw [show (2860:Nat)=2684+(2860-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3779 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3696 := by
  rw [show (2861:Nat)=2684+(2861-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3787 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3697 := by
  rw [show (2862:Nat)=2684+(2862-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3788 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3698 := by
  rw [show (2863:Nat)=2684+(2863-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3789 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3701 := by
  rw [show (2864:Nat)=2684+(2864-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3790 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3702 := by
  rw [show (2865:Nat)=2684+(2865-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3791 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3705 := by
  rw [show (2866:Nat)=2684+(2866-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3792 : CycleSubmission.Artifact.artifact.instructionPC 2867 = 3706 := by
  rw [show (2867:Nat)=2684+(2867-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3793 : CycleSubmission.Artifact.artifact.instructionPC 2868 = 3707 := by
  rw [show (2868:Nat)=2684+(2868-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3794 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3710 := by
  rw [show (2869:Nat)=2684+(2869-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3795 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3713 := by
  rw [show (2870:Nat)=2684+(2870-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3796 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3714 := by
  rw [show (2871:Nat)=2684+(2871-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3797 : CycleSubmission.Artifact.artifact.instructionPC 2872 = 3715 := by
  rw [show (2872:Nat)=2684+(2872-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3798 : CycleSubmission.Artifact.artifact.instructionPC 2872 = 3715 := fixedPC3797

@[simp] theorem fixedPC3799 : CycleSubmission.Artifact.artifact.instructionPC 2872 = 3715 := fixedPC3797

@[simp] theorem fixedPC3800 : CycleSubmission.Artifact.artifact.instructionPC 2873 = 3716 := by
  rw [show (2873:Nat)=2684+(2873-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3801 : CycleSubmission.Artifact.artifact.instructionPC 2874 = 3717 := by
  rw [show (2874:Nat)=2684+(2874-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3802 : CycleSubmission.Artifact.artifact.instructionPC 2875 = 3718 := by
  rw [show (2875:Nat)=2684+(2875-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3803 : CycleSubmission.Artifact.artifact.instructionPC 2876 = 3721 := by
  rw [show (2876:Nat)=2684+(2876-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3804 : CycleSubmission.Artifact.artifact.instructionPC 2877 = 3724 := by
  rw [show (2877:Nat)=2684+(2877-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : CycleSubmission.Artifact.artifact.instructionPC 2720 = 3501 := by
  rw [show (2720:Nat)=2684+(2720-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3115 : CycleSubmission.Artifact.artifact.instructionPC 2721 = 3504 := by
  rw [show (2721:Nat)=2684+(2721-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3116 : CycleSubmission.Artifact.artifact.instructionPC 2722 = 3505 := by
  rw [show (2722:Nat)=2684+(2722-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3117 : CycleSubmission.Artifact.artifact.instructionPC 2723 = 3508 := by
  rw [show (2723:Nat)=2684+(2723-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3118 : CycleSubmission.Artifact.artifact.instructionPC 2724 = 3509 := by
  rw [show (2724:Nat)=2684+(2724-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3119 : CycleSubmission.Artifact.artifact.instructionPC 2725 = 3512 := by
  rw [show (2725:Nat)=2684+(2725-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3454 := by
  rw [show (2692:Nat)=2684+(2692-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3462 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3462 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2696 (by rfl)

@[simp] theorem fixedPC3805 : CycleSubmission.Artifact.artifact.instructionPC 2726 = 3513 := by
  rw [show (2726:Nat)=2684+(2726-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3806 : CycleSubmission.Artifact.artifact.instructionPC 2727 = 3515 := by
  rw [show (2727:Nat)=2684+(2727-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3807 : CycleSubmission.Artifact.artifact.instructionPC 2728 = 3516 := by
  rw [show (2728:Nat)=2684+(2728-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3808 : CycleSubmission.Artifact.artifact.instructionPC 2729 = 3519 := by
  rw [show (2729:Nat)=2684+(2729-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPCs8 : CycleSubmission.Artifact.artifact.instructionPC 2730 = 3520 := by
  rw [show (2730:Nat)=2684+(2730-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3809 : CycleSubmission.Artifact.artifact.instructionPC 2731 = 3521 := by
  rw [show (2731:Nat)=2684+(2731-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3810 : CycleSubmission.Artifact.artifact.instructionPC 2732 = 3524 := by
  rw [show (2732:Nat)=2684+(2732-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3811 : CycleSubmission.Artifact.artifact.instructionPC 2733 = 3525 := by
  rw [show (2733:Nat)=2684+(2733-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3812 : CycleSubmission.Artifact.artifact.instructionPC 2734 = 3527 := by
  rw [show (2734:Nat)=2684+(2734-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3813 : CycleSubmission.Artifact.artifact.instructionPC 2735 = 3528 := by
  rw [show (2735:Nat)=2684+(2735-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3814 : CycleSubmission.Artifact.artifact.instructionPC 2736 = 3529 := by
  rw [show (2736:Nat)=2684+(2736-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3815 : CycleSubmission.Artifact.artifact.instructionPC 2737 = 3530 := by
  rw [show (2737:Nat)=2684+(2737-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3816 : CycleSubmission.Artifact.artifact.instructionPC 2737 = 3530 := by
  rw [show (2737:Nat)=2684+(2737-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3817 : CycleSubmission.Artifact.artifact.instructionPC 2738 = 3531 := by
  rw [show (2738:Nat)=2684+(2738-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3818 : CycleSubmission.Artifact.artifact.instructionPC 2739 = 3534 := by
  rw [show (2739:Nat)=2684+(2739-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3819 : CycleSubmission.Artifact.artifact.instructionPC 2740 = 3535 := by
  rw [show (2740:Nat)=2684+(2740-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3820 : CycleSubmission.Artifact.artifact.instructionPC 2741 = 3536 := by
  rw [show (2741:Nat)=2684+(2741-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3821 : CycleSubmission.Artifact.artifact.instructionPC 2742 = 3537 := by
  rw [show (2742:Nat)=2684+(2742-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3822 : CycleSubmission.Artifact.artifact.instructionPC 2743 = 3539 := by
  rw [show (2743:Nat)=2684+(2743-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3823 : CycleSubmission.Artifact.artifact.instructionPC 2744 = 3540 := by
  rw [show (2744:Nat)=2684+(2744-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3824 : CycleSubmission.Artifact.artifact.instructionPC 2745 = 3541 := by
  rw [show (2745:Nat)=2684+(2745-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3825 : CycleSubmission.Artifact.artifact.instructionPC 2746 = 3542 := by
  rw [show (2746:Nat)=2684+(2746-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3826 : CycleSubmission.Artifact.artifact.instructionPC 2747 = 3545 := by
  rw [show (2747:Nat)=2684+(2747-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3827 : CycleSubmission.Artifact.artifact.instructionPC 2748 = 3546 := by
  rw [show (2748:Nat)=2684+(2748-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3828 : CycleSubmission.Artifact.artifact.instructionPC 2749 = 3547 := by
  rw [show (2749:Nat)=2684+(2749-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3829 : CycleSubmission.Artifact.artifact.instructionPC 2750 = 3548 := by
  rw [show (2750:Nat)=2684+(2750-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3830 : CycleSubmission.Artifact.artifact.instructionPC 2751 = 3549 := by
  rw [show (2751:Nat)=2684+(2751-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3831 : CycleSubmission.Artifact.artifact.instructionPC 2752 = 3552 := by
  rw [show (2752:Nat)=2684+(2752-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3832 : CycleSubmission.Artifact.artifact.instructionPC 2753 = 3553 := by
  rw [show (2753:Nat)=2684+(2753-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3833 : CycleSubmission.Artifact.artifact.instructionPC 2754 = 3554 := by
  rw [show (2754:Nat)=2684+(2754-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3834 : CycleSubmission.Artifact.artifact.instructionPC 2754 = 3554 := by
  rw [show (2754:Nat)=2684+(2754-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3835 : CycleSubmission.Artifact.artifact.instructionPC 2755 = 3555 := by
  rw [show (2755:Nat)=2684+(2755-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3836 : CycleSubmission.Artifact.artifact.instructionPC 2756 = 3556 := by
  rw [show (2756:Nat)=2684+(2756-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3837 : CycleSubmission.Artifact.artifact.instructionPC 2757 = 3557 := by
  rw [show (2757:Nat)=2684+(2757-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3838 : CycleSubmission.Artifact.artifact.instructionPC 2758 = 3558 := by
  rw [show (2758:Nat)=2684+(2758-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3839 : CycleSubmission.Artifact.artifact.instructionPC 2759 = 3560 := by
  rw [show (2759:Nat)=2684+(2759-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3840 : CycleSubmission.Artifact.artifact.instructionPC 2760 = 3561 := by
  rw [show (2760:Nat)=2684+(2760-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3841 : CycleSubmission.Artifact.artifact.instructionPC 2761 = 3562 := by
  rw [show (2761:Nat)=2684+(2761-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3842 : CycleSubmission.Artifact.artifact.instructionPC 2762 = 3563 := by
  rw [show (2762:Nat)=2684+(2762-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3843 : CycleSubmission.Artifact.artifact.instructionPC 2763 = 3566 := by
  rw [show (2763:Nat)=2684+(2763-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3844 : CycleSubmission.Artifact.artifact.instructionPC 2764 = 3567 := by
  rw [show (2764:Nat)=2684+(2764-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3845 : CycleSubmission.Artifact.artifact.instructionPC 2765 = 3568 := by
  rw [show (2765:Nat)=2684+(2765-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3846 : CycleSubmission.Artifact.artifact.instructionPC 2766 = 3569 := by
  rw [show (2766:Nat)=2684+(2766-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3847 : CycleSubmission.Artifact.artifact.instructionPC 2767 = 3570 := by
  rw [show (2767:Nat)=2684+(2767-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3848 : CycleSubmission.Artifact.artifact.instructionPC 2768 = 3573 := by
  rw [show (2768:Nat)=2684+(2768-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3849 : CycleSubmission.Artifact.artifact.instructionPC 2769 = 3574 := by
  rw [show (2769:Nat)=2684+(2769-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3850 : CycleSubmission.Artifact.artifact.instructionPC 2770 = 3575 := by
  rw [show (2770:Nat)=2684+(2770-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3851 : CycleSubmission.Artifact.artifact.instructionPC 2771 = 3576 := by
  rw [show (2771:Nat)=2684+(2771-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3852 : CycleSubmission.Artifact.artifact.instructionPC 2771 = 3576 := by
  rw [show (2771:Nat)=2684+(2771-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3853 : CycleSubmission.Artifact.artifact.instructionPC 2772 = 3577 := by
  rw [show (2772:Nat)=2684+(2772-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3854 : CycleSubmission.Artifact.artifact.instructionPC 2773 = 3578 := by
  rw [show (2773:Nat)=2684+(2773-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3855 : CycleSubmission.Artifact.artifact.instructionPC 2774 = 3579 := by
  rw [show (2774:Nat)=2684+(2774-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3856 : CycleSubmission.Artifact.artifact.instructionPC 2775 = 3581 := by
  rw [show (2775:Nat)=2684+(2775-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3857 : CycleSubmission.Artifact.artifact.instructionPC 2776 = 3582 := by
  rw [show (2776:Nat)=2684+(2776-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3858 : CycleSubmission.Artifact.artifact.instructionPC 2777 = 3583 := by
  rw [show (2777:Nat)=2684+(2777-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3859 : CycleSubmission.Artifact.artifact.instructionPC 2778 = 3584 := by
  rw [show (2778:Nat)=2684+(2778-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3860 : CycleSubmission.Artifact.artifact.instructionPC 2779 = 3587 := by
  rw [show (2779:Nat)=2684+(2779-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3861 : CycleSubmission.Artifact.artifact.instructionPC 2780 = 3588 := by
  rw [show (2780:Nat)=2684+(2780-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3862 : CycleSubmission.Artifact.artifact.instructionPC 2781 = 3589 := by
  rw [show (2781:Nat)=2684+(2781-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3863 : CycleSubmission.Artifact.artifact.instructionPC 2782 = 3590 := by
  rw [show (2782:Nat)=2684+(2782-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3864 : CycleSubmission.Artifact.artifact.instructionPC 2783 = 3591 := by
  rw [show (2783:Nat)=2684+(2783-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3865 : CycleSubmission.Artifact.artifact.instructionPC 2784 = 3594 := by
  rw [show (2784:Nat)=2684+(2784-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3866 : CycleSubmission.Artifact.artifact.instructionPC 2785 = 3595 := by
  rw [show (2785:Nat)=2684+(2785-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3867 : CycleSubmission.Artifact.artifact.instructionPC 2786 = 3596 := by
  rw [show (2786:Nat)=2684+(2786-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3868 : CycleSubmission.Artifact.artifact.instructionPC 2787 = 3597 := by
  rw [show (2787:Nat)=2684+(2787-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3869 : CycleSubmission.Artifact.artifact.instructionPC 2788 = 3598 := by
  rw [show (2788:Nat)=2684+(2788-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3871 : CycleSubmission.Artifact.artifact.instructionPC 2788 = 3598 := by
  rw [show (2788:Nat)=2684+(2788-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3872 : CycleSubmission.Artifact.artifact.instructionPC 2789 = 3599 := by
  rw [show (2789:Nat)=2684+(2789-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3873 : CycleSubmission.Artifact.artifact.instructionPC 2790 = 3600 := by
  rw [show (2790:Nat)=2684+(2790-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3874 : CycleSubmission.Artifact.artifact.instructionPC 2791 = 3602 := by
  rw [show (2791:Nat)=2684+(2791-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3875 : CycleSubmission.Artifact.artifact.instructionPC 2792 = 3603 := by
  rw [show (2792:Nat)=2684+(2792-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3876 : CycleSubmission.Artifact.artifact.instructionPC 2793 = 3604 := by
  rw [show (2793:Nat)=2684+(2793-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3877 : CycleSubmission.Artifact.artifact.instructionPC 2794 = 3605 := by
  rw [show (2794:Nat)=2684+(2794-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3878 : CycleSubmission.Artifact.artifact.instructionPC 2795 = 3608 := by
  rw [show (2795:Nat)=2684+(2795-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3879 : CycleSubmission.Artifact.artifact.instructionPC 2796 = 3609 := by
  rw [show (2796:Nat)=2684+(2796-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3880 : CycleSubmission.Artifact.artifact.instructionPC 2797 = 3610 := by
  rw [show (2797:Nat)=2684+(2797-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3881 : CycleSubmission.Artifact.artifact.instructionPC 2798 = 3611 := by
  rw [show (2798:Nat)=2684+(2798-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3882 : CycleSubmission.Artifact.artifact.instructionPC 2799 = 3612 := by
  rw [show (2799:Nat)=2684+(2799-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3883 : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3615 := by
  rw [show (2800:Nat)=2684+(2800-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3884 : CycleSubmission.Artifact.artifact.instructionPC 2801 = 3616 := by
  rw [show (2801:Nat)=2684+(2801-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3885 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3617 := by
  rw [show (2802:Nat)=2684+(2802-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3886 : CycleSubmission.Artifact.artifact.instructionPC 2803 = 3618 := by
  rw [show (2803:Nat)=2684+(2803-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3887 : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3619 := by
  rw [show (2804:Nat)=2684+(2804-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3888 : CycleSubmission.Artifact.artifact.instructionPC 2805 = 3620 := by
  rw [show (2805:Nat)=2684+(2805-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3889 : CycleSubmission.Artifact.artifact.instructionPC 2805 = 3620 := by
  rw [show (2805:Nat)=2684+(2805-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3620 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2805 = 3620 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2805 (by rfl)

@[simp] theorem fixedPC3890 : CycleSubmission.Artifact.artifact.instructionPC 2806 = 3621 := by
  rw [show (2806:Nat)=2684+(2806-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3891 : CycleSubmission.Artifact.artifact.instructionPC 2807 = 3622 := by
  rw [show (2807:Nat)=2684+(2807-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3892 : CycleSubmission.Artifact.artifact.instructionPC 2808 = 3624 := by
  rw [show (2808:Nat)=2684+(2808-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3893 : CycleSubmission.Artifact.artifact.instructionPC 2809 = 3625 := by
  rw [show (2809:Nat)=2684+(2809-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3894 : CycleSubmission.Artifact.artifact.instructionPC 2810 = 3626 := by
  rw [show (2810:Nat)=2684+(2810-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3895 : CycleSubmission.Artifact.artifact.instructionPC 2811 = 3627 := by
  rw [show (2811:Nat)=2684+(2811-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3896 : CycleSubmission.Artifact.artifact.instructionPC 2812 = 3630 := by
  rw [show (2812:Nat)=2684+(2812-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3897 : CycleSubmission.Artifact.artifact.instructionPC 2813 = 3631 := by
  rw [show (2813:Nat)=2684+(2813-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3898 : CycleSubmission.Artifact.artifact.instructionPC 2814 = 3632 := by
  rw [show (2814:Nat)=2684+(2814-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3899 : CycleSubmission.Artifact.artifact.instructionPC 2815 = 3633 := by
  rw [show (2815:Nat)=2684+(2815-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3900 : CycleSubmission.Artifact.artifact.instructionPC 2816 = 3634 := by
  rw [show (2816:Nat)=2684+(2816-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3901 : CycleSubmission.Artifact.artifact.instructionPC 2817 = 3637 := by
  rw [show (2817:Nat)=2684+(2817-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3902 : CycleSubmission.Artifact.artifact.instructionPC 2818 = 3638 := by
  rw [show (2818:Nat)=2684+(2818-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3903 : CycleSubmission.Artifact.artifact.instructionPC 2819 = 3639 := by
  rw [show (2819:Nat)=2684+(2819-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3904 : CycleSubmission.Artifact.artifact.instructionPC 2820 = 3640 := by
  rw [show (2820:Nat)=2684+(2820-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3905 : CycleSubmission.Artifact.artifact.instructionPC 2821 = 3641 := by
  rw [show (2821:Nat)=2684+(2821-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3906 : CycleSubmission.Artifact.artifact.instructionPC 2822 = 3642 := by
  rw [show (2822:Nat)=2684+(2822-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3907 : CycleSubmission.Artifact.artifact.instructionPC 2823 = 3643 := by
  rw [show (2823:Nat)=2684+(2823-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3908 : CycleSubmission.Artifact.artifact.instructionPC 2823 = 3643 := by
  rw [show (2823:Nat)=2684+(2823-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3909 : CycleSubmission.Artifact.artifact.instructionPC 2824 = 3645 := by
  rw [show (2824:Nat)=2684+(2824-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3910 : CycleSubmission.Artifact.artifact.instructionPC 2825 = 3646 := by
  rw [show (2825:Nat)=2684+(2825-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3911 : CycleSubmission.Artifact.artifact.instructionPC 2826 = 3647 := by
  rw [show (2826:Nat)=2684+(2826-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3912 : CycleSubmission.Artifact.artifact.instructionPC 2827 = 3648 := by
  rw [show (2827:Nat)=2684+(2827-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3913 : CycleSubmission.Artifact.artifact.instructionPC 2828 = 3651 := by
  rw [show (2828:Nat)=2684+(2828-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3914 : CycleSubmission.Artifact.artifact.instructionPC 2829 = 3652 := by
  rw [show (2829:Nat)=2684+(2829-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3915 : CycleSubmission.Artifact.artifact.instructionPC 2830 = 3653 := by
  rw [show (2830:Nat)=2684+(2830-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3916 : CycleSubmission.Artifact.artifact.instructionPC 2831 = 3654 := by
  rw [show (2831:Nat)=2684+(2831-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3917 : CycleSubmission.Artifact.artifact.instructionPC 2832 = 3655 := by
  rw [show (2832:Nat)=2684+(2832-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3918 : CycleSubmission.Artifact.artifact.instructionPC 2833 = 3658 := by
  rw [show (2833:Nat)=2684+(2833-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3919 : CycleSubmission.Artifact.artifact.instructionPC 2834 = 3659 := by
  rw [show (2834:Nat)=2684+(2834-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3920 : CycleSubmission.Artifact.artifact.instructionPC 2835 = 3660 := by
  rw [show (2835:Nat)=2684+(2835-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2836 = 3661 := by
  rw [show (2836:Nat)=2684+(2836-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2837 = 3662 := by
  rw [show (2837:Nat)=2684+(2837-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2838 = 3663 := by
  rw [show (2838:Nat)=2684+(2838-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2839 = 3664 := by
  rw [show (2839:Nat)=2684+(2839-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2840 = 3665 := by
  rw [show (2840:Nat)=2684+(2840-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2840 = 3665 := by
  rw [show (2840:Nat)=2684+(2840-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2841 = 3666 := by
  rw [show (2841:Nat)=2684+(2841-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2842 = 3667 := by
  rw [show (2842:Nat)=2684+(2842-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3929 : CycleSubmission.Artifact.artifact.instructionPC 2843 = 3668 := by
  rw [show (2843:Nat)=2684+(2843-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3930 : CycleSubmission.Artifact.artifact.instructionPC 2844 = 3671 := by
  rw [show (2844:Nat)=2684+(2844-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3931 : CycleSubmission.Artifact.artifact.instructionPC 2845 = 3672 := by
  rw [show (2845:Nat)=2684+(2845-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3932 : CycleSubmission.Artifact.artifact.instructionPC 2846 = 3673 := by
  rw [show (2846:Nat)=2684+(2846-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3933 : CycleSubmission.Artifact.artifact.instructionPC 2847 = 3674 := by
  rw [show (2847:Nat)=2684+(2847-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3934 : CycleSubmission.Artifact.artifact.instructionPC 2848 = 3675 := by
  rw [show (2848:Nat)=2684+(2848-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3935 : CycleSubmission.Artifact.artifact.instructionPC 2849 = 3678 := by
  rw [show (2849:Nat)=2684+(2849-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3936 : CycleSubmission.Artifact.artifact.instructionPC 2850 = 3679 := by
  rw [show (2850:Nat)=2684+(2850-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3937 : CycleSubmission.Artifact.artifact.instructionPC 2851 = 3680 := by
  rw [show (2851:Nat)=2684+(2851-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3938 : CycleSubmission.Artifact.artifact.instructionPC 2852 = 3681 := by
  rw [show (2852:Nat)=2684+(2852-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3939 : CycleSubmission.Artifact.artifact.instructionPC 2853 = 3682 := by
  rw [show (2853:Nat)=2684+(2853-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3940 : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3683 := by
  rw [show (2854:Nat)=2684+(2854-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3941 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3684 := by
  rw [show (2855:Nat)=2684+(2855-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3942 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3687 := by
  rw [show (2856:Nat)=2684+(2856-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3943 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3688 := by
  rw [show (2857:Nat)=2684+(2857-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3944 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3688 := by
  rw [show (2857:Nat)=2684+(2857-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3945 : CycleSubmission.Artifact.artifact.instructionPC 2858 = 3689 := by
  rw [show (2858:Nat)=2684+(2858-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3946 : CycleSubmission.Artifact.artifact.instructionPC 2859 = 3692 := by
  rw [show (2859:Nat)=2684+(2859-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3947 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3693 := by
  rw [show (2860:Nat)=2684+(2860-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3948 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3696 := by
  rw [show (2861:Nat)=2684+(2861-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3949 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3714 := by
  rw [show (2871:Nat)=2684+(2871-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3950 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3714 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : CycleSubmission.Artifact.artifact.instructionPC 2872 = 3715 := by
  rw [show (2872:Nat)=2684+(2872-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3952 : CycleSubmission.Artifact.artifact.instructionPC 2873 = 3716 := by
  rw [show (2873:Nat)=2684+(2873-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3953 : CycleSubmission.Artifact.artifact.instructionPC 2874 = 3717 := by
  rw [show (2874:Nat)=2684+(2874-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3954 : CycleSubmission.Artifact.artifact.instructionPC 2875 = 3718 := by
  rw [show (2875:Nat)=2684+(2875-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3955 : CycleSubmission.Artifact.artifact.instructionPC 2876 = 3721 := by
  rw [show (2876:Nat)=2684+(2876-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3956 : CycleSubmission.Artifact.artifact.instructionPC 2877 = 3724 := by
  rw [show (2877:Nat)=2684+(2877-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3957 : CycleSubmission.Artifact.artifact.instructionPC 2878 = 3725 := by
  rw [show (2878:Nat)=2684+(2878-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4190 : CycleSubmission.Artifact.artifact.instructionPC 2706 = 3477 := by
  rw [show (2706:Nat)=2684+(2706-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4193 : CycleSubmission.Artifact.artifact.instructionPC 2707 = 3478 := by
  rw [show (2707:Nat)=2684+(2707-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4194 : CycleSubmission.Artifact.artifact.instructionPC 2708 = 3481 := by
  rw [show (2708:Nat)=2684+(2708-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4547 : CycleSubmission.Artifact.artifact.instructionPC 2879 = 3726 := by
  rw [show (2879:Nat)=2684+(2879-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4548 : CycleSubmission.Artifact.artifact.instructionPC 2880 = 3727 := by
  rw [show (2880:Nat)=2684+(2880-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC3999 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3454 := by
  rw [show (2692:Nat)=2684+(2692-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3462 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3462 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2696 (by rfl)

@[simp] theorem fixedPC4000 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3457 := by
  rw [show (2693:Nat)=2684+(2693-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4001 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3458 := by
  rw [show (2694:Nat)=2684+(2694-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4002 : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3461 := by
  rw [show (2695:Nat)=2684+(2695-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4003 : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3462 := by
  rw [show (2696:Nat)=2684+(2696-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4004 : CycleSubmission.Artifact.artifact.instructionPC 2697 = 3463 := by
  rw [show (2697:Nat)=2684+(2697-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4005 : CycleSubmission.Artifact.artifact.instructionPC 2698 = 3466 := by
  rw [show (2698:Nat)=2684+(2698-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4006 : CycleSubmission.Artifact.artifact.instructionPC 2699 = 3467 := by
  rw [show (2699:Nat)=2684+(2699-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4007 : CycleSubmission.Artifact.artifact.instructionPC 2700 = 3469 := by
  rw [show (2700:Nat)=2684+(2700-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4008 : CycleSubmission.Artifact.artifact.instructionPC 2701 = 3470 := by
  rw [show (2701:Nat)=2684+(2701-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4009 : CycleSubmission.Artifact.artifact.instructionPC 2702 = 3471 := by
  rw [show (2702:Nat)=2684+(2702-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4010 : CycleSubmission.Artifact.artifact.instructionPC 2703 = 3472 := by
  rw [show (2703:Nat)=2684+(2703-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4011 : CycleSubmission.Artifact.artifact.instructionPC 2704 = 3473 := by
  rw [show (2704:Nat)=2684+(2704-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4012 : CycleSubmission.Artifact.artifact.instructionPC 2705 = 3476 := by
  rw [show (2705:Nat)=2684+(2705-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2883 : CycleSubmission.Artifact.artifact.instructionPC 2680 = 3438 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : CycleSubmission.Artifact.artifact.instructionPC 2681 = 3439 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : CycleSubmission.Artifact.artifact.instructionPC 2682 = 3440 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3441 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3442 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3443 := by
  rw [show (2685:Nat)=2684+(2685-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2890 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3444 := by
  rw [show (2686:Nat)=2684+(2686-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2891 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3447 := by
  rw [show (2687:Nat)=2684+(2687-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2892 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3448 := by
  rw [show (2688:Nat)=2684+(2688-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2893 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3448 := by
  rw [show (2688:Nat)=2684+(2688-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2894 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3449 := by
  rw [show (2689:Nat)=2684+(2689-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2895 : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3452 := by
  rw [show (2690:Nat)=2684+(2690-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2896 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3453 := by
  rw [show (2691:Nat)=2684+(2691-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2930 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3454 := by
  rw [show (2692:Nat)=2684+(2692-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2931 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3457 := by
  rw [show (2693:Nat)=2684+(2693-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2932 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3458 := by
  rw [show (2694:Nat)=2684+(2694-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2933 : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3461 := by
  rw [show (2695:Nat)=2684+(2695-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2934 : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3462 := by
  rw [show (2696:Nat)=2684+(2696-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2935 : CycleSubmission.Artifact.artifact.instructionPC 2697 = 3463 := by
  rw [show (2697:Nat)=2684+(2697-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2936 : CycleSubmission.Artifact.artifact.instructionPC 2698 = 3466 := by
  rw [show (2698:Nat)=2684+(2698-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2937 : CycleSubmission.Artifact.artifact.instructionPC 2699 = 3467 := by
  rw [show (2699:Nat)=2684+(2699-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2938 : CycleSubmission.Artifact.artifact.instructionPC 2700 = 3469 := by
  rw [show (2700:Nat)=2684+(2700-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2939 : CycleSubmission.Artifact.artifact.instructionPC 2701 = 3470 := by
  rw [show (2701:Nat)=2684+(2701-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2940 : CycleSubmission.Artifact.artifact.instructionPC 2702 = 3471 := by
  rw [show (2702:Nat)=2684+(2702-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2941 : CycleSubmission.Artifact.artifact.instructionPC 2703 = 3472 := by
  rw [show (2703:Nat)=2684+(2703-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2942 : CycleSubmission.Artifact.artifact.instructionPC 2704 = 3473 := by
  rw [show (2704:Nat)=2684+(2704-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2943 : CycleSubmission.Artifact.artifact.instructionPC 2705 = 3476 := by
  rw [show (2705:Nat)=2684+(2705-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3698 := by
  rw [show (2863:Nat)=2684+(2863-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3701 := by
  rw [show (2864:Nat)=2684+(2864-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3702 := by
  rw [show (2865:Nat)=2684+(2865-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3705 := by
  rw [show (2866:Nat)=2684+(2866-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2867 = 3706 := by
  rw [show (2867:Nat)=2684+(2867-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2868 = 3707 := by
  rw [show (2868:Nat)=2684+(2868-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3710 := by
  rw [show (2869:Nat)=2684+(2869-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3713 := by
  rw [show (2870:Nat)=2684+(2870-2684) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

end CycleSubmission.Global.Fast
