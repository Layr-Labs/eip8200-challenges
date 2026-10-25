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
  [opAt 2712 .JUMPDEST,
   pushAt 2713 2 2688,
   opAt 2714 .MLOAD,
   pushAt 2715 1 128,
   opAt 2716 .EQ,
   pushAt 2717 2 3462,
   opAt 2718 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2712 .JUMPDEST,
   pushAt 2713 2 2688,
   opAt 2714 .MLOAD,
   pushAt 2715 1 128,
   opAt 2716 .EQ,
   pushAt 2717 2 3462,
   opAt 2718 .JUMPI,
   opAt 2685 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2719 .JUMPDEST,
   pushAt 2720 2 2336,
   opAt 2721 .MLOAD,
   pushAt 2722 1 224,
   opAt 2723 .MLOAD,
   opAt 2724 (.Dup ⟨0, by decide⟩),
   opAt 2725 (.Dup ⟨2, by decide⟩),
   opAt 2726 .SUB,
   pushAt 2727 2 2016,
   opAt 2728 .MSTORE,
   opAt 2729 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2730 (.Dup ⟨0, by decide⟩),
   pushAt 2731 1 192,
   opAt 2732 .MLOAD,
   opAt 2733 .ADD,
   opAt 2734 (.Dup ⟨0, by decide⟩),
   pushAt 2735 2 2304,
   opAt 2736 .MLOAD,
   opAt 2737 (.Dup ⟨1, by decide⟩),
   opAt 2738 (.Dup ⟨1, by decide⟩),
   opAt 2739 .SUB,
   pushAt 2740 2 1984,
   opAt 2741 .MSTORE,
   opAt 2742 .LT,
   opAt 2743 (.Swap ⟨1, by decide⟩),
   opAt 2744 .GT,
   opAt 2745 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2746 (.Dup ⟨0, by decide⟩),
   pushAt 2747 1 160,
   opAt 2748 .MLOAD,
   opAt 2749 .ADD,
   opAt 2750 (.Dup ⟨0, by decide⟩),
   pushAt 2751 2 2272,
   opAt 2752 .MLOAD,
   opAt 2753 (.Dup ⟨1, by decide⟩),
   opAt 2754 (.Dup ⟨1, by decide⟩),
   opAt 2755 .SUB,
   pushAt 2756 2 1952,
   opAt 2757 .MSTORE,
   opAt 2758 .LT,
   opAt 2759 (.Swap ⟨1, by decide⟩),
   opAt 2760 .GT,
   opAt 2761 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2762 (.Dup ⟨0, by decide⟩),
   pushAt 2763 1 128,
   opAt 2764 .MLOAD,
   opAt 2765 .ADD,
   opAt 2766 (.Dup ⟨0, by decide⟩),
   pushAt 2767 2 2240,
   opAt 2768 .MLOAD,
   opAt 2769 (.Dup ⟨1, by decide⟩),
   opAt 2770 (.Dup ⟨1, by decide⟩),
   opAt 2771 .SUB,
   pushAt 2772 2 1920,
   opAt 2773 .MSTORE,
   opAt 2774 .LT,
   opAt 2775 (.Swap ⟨1, by decide⟩),
   opAt 2776 .GT,
   opAt 2777 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2778 (.Dup ⟨0, by decide⟩),
   pushAt 2779 1 96,
   opAt 2780 .MLOAD,
   opAt 2781 .ADD,
   opAt 2782 (.Dup ⟨0, by decide⟩),
   pushAt 2783 2 2208,
   opAt 2784 .MLOAD,
   opAt 2785 (.Dup ⟨1, by decide⟩),
   opAt 2786 (.Dup ⟨1, by decide⟩),
   opAt 2787 .SUB,
   pushAt 2788 2 1888,
   opAt 2789 .MSTORE,
   opAt 2790 .LT,
   opAt 2791 (.Swap ⟨1, by decide⟩),
   opAt 2792 .GT,
   opAt 2793 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2794 .JUMPDEST,
   opAt 2795 (.Dup ⟨0, by decide⟩),
   pushAt 2796 1 64,
   opAt 2797 .MLOAD,
   opAt 2798 .ADD,
   opAt 2799 (.Dup ⟨0, by decide⟩),
   pushAt 2800 2 2176,
   opAt 2801 .MLOAD,
   opAt 2802 (.Dup ⟨1, by decide⟩),
   opAt 2803 (.Dup ⟨1, by decide⟩),
   opAt 2804 .SUB,
   pushAt 2805 2 1856,
   opAt 2806 .MSTORE,
   opAt 2807 .LT,
   opAt 2808 (.Swap ⟨1, by decide⟩),
   opAt 2809 .GT,
   opAt 2810 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2811 (.Dup ⟨0, by decide⟩),
   pushAt 2812 1 32,
   opAt 2813 .MLOAD,
   opAt 2814 .ADD,
   opAt 2815 (.Dup ⟨0, by decide⟩),
   pushAt 2816 2 2144,
   opAt 2817 .MLOAD,
   opAt 2818 (.Dup ⟨1, by decide⟩),
   opAt 2819 (.Dup ⟨1, by decide⟩),
   opAt 2820 .SUB,
   pushAt 2821 2 1824,
   opAt 2822 .MSTORE,
   opAt 2823 .LT,
   opAt 2824 (.Swap ⟨1, by decide⟩),
   opAt 2825 .GT,
   opAt 2826 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2827 (.Dup ⟨0, by decide⟩),
   pushAt 2828 0 0,
   opAt 2829 .MLOAD,
   opAt 2830 .ADD,
   opAt 2831 (.Dup ⟨0, by decide⟩),
   pushAt 2832 2 2112,
   opAt 2833 .MLOAD,
   opAt 2834 (.Dup ⟨1, by decide⟩),
   opAt 2835 (.Dup ⟨1, by decide⟩),
   opAt 2836 .SUB,
   pushAt 2837 2 1792,
   opAt 2838 .MSTORE,
   opAt 2839 .LT,
   opAt 2840 (.Swap ⟨1, by decide⟩),
   opAt 2841 .GT,
   opAt 2842 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2843 .ISZERO,
   pushAt 2844 2 2080,
   opAt 2845 .MLOAD,
   opAt 2846 .OR,
   pushAt 2847 2 3717,
   opAt 2848 .JUMPI,
   opAt 2863 .JUMPDEST,
   pushAt 2864 2 1792,
   pushAt 2865 2 2688,
   opAt 2866 .MLOAD,
   opAt 2867 (.Swap ⟨1, by decide⟩),
   opAt 2868 .MCOPY,
   opAt 2869 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2843 .ISZERO,
   pushAt 2844 2 2080,
   opAt 2845 .MLOAD,
   opAt 2846 .OR,
   pushAt 2847 2 3717,
   opAt 2848 .JUMPI,
   pushAt 2849 2 3706,
   opAt 2850 .JUMP,
   opAt 2856 .JUMPDEST,
   pushAt 2857 2 2112,
   pushAt 2858 2 2688,
   opAt 2859 .MLOAD,
   opAt 2860 (.Swap ⟨1, by decide⟩),
   opAt 2861 .MCOPY,
   opAt 2862 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2686 2 2208,
   opAt 2687 .MLOAD,
   pushAt 2688 1 96,
   opAt 2689 .MLOAD,
   opAt 2690 (.Dup ⟨0, by decide⟩),
   opAt 2691 (.Dup ⟨2, by decide⟩),
   opAt 2692 .SUB,
   pushAt 2693 2 1888,
   opAt 2694 .MSTORE,
   opAt 2695 .GT,
   pushAt 2696 2 3620,
   opAt 2697 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2794 .JUMPDEST,
   opAt 2795 (.Dup ⟨0, by decide⟩),
   pushAt 2796 1 64,
   opAt 2797 .MLOAD,
   opAt 2798 .ADD,
   opAt 2799 (.Dup ⟨0, by decide⟩),
   pushAt 2800 2 2176,
   opAt 2801 .MLOAD,
   opAt 2802 (.Dup ⟨1, by decide⟩),
   opAt 2803 (.Dup ⟨1, by decide⟩),
   opAt 2804 .SUB,
   pushAt 2805 2 1856,
   opAt 2806 .MSTORE,
   opAt 2807 .LT,
   opAt 2808 (.Swap ⟨1, by decide⟩),
   opAt 2809 .GT,
   opAt 2810 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2811 (.Dup ⟨0, by decide⟩),
   pushAt 2812 1 32,
   opAt 2813 .MLOAD,
   opAt 2814 .ADD,
   opAt 2815 (.Dup ⟨0, by decide⟩),
   pushAt 2816 2 2144,
   opAt 2817 .MLOAD,
   opAt 2818 (.Dup ⟨1, by decide⟩),
   opAt 2819 (.Dup ⟨1, by decide⟩),
   opAt 2820 .SUB,
   pushAt 2821 2 1824,
   opAt 2822 .MSTORE,
   opAt 2823 .LT,
   opAt 2824 (.Swap ⟨1, by decide⟩),
   opAt 2825 .GT,
   opAt 2826 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2827 (.Dup ⟨0, by decide⟩),
   pushAt 2828 0 0,
   opAt 2829 .MLOAD,
   opAt 2830 .ADD,
   opAt 2831 (.Dup ⟨0, by decide⟩),
   pushAt 2832 2 2112,
   opAt 2833 .MLOAD,
   opAt 2834 (.Dup ⟨1, by decide⟩),
   opAt 2835 (.Dup ⟨1, by decide⟩),
   opAt 2836 .SUB,
   pushAt 2837 2 1792,
   opAt 2838 .MSTORE,
   opAt 2839 .LT,
   opAt 2840 (.Swap ⟨1, by decide⟩),
   opAt 2841 .GT,
   opAt 2842 .OR]

private theorem cycleAnchor : CycleSubmission.Artifact.artifact.instructionPC 2673 = 3442 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem fixedPC3777 : CycleSubmission.Artifact.artifact.instructionPC 2708 = 3500 := by
  rw [show (2708:Nat)=2673+(2708-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3508 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2712 = 3508 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2712 (by rfl)

@[simp] theorem fixedPC3778 : CycleSubmission.Artifact.artifact.instructionPC 2849 = 3693 := by
  rw [show (2849:Nat)=2673+(2849-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3779 : CycleSubmission.Artifact.artifact.instructionPC 2850 = 3696 := by
  rw [show (2850:Nat)=2673+(2850-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3787 : CycleSubmission.Artifact.artifact.instructionPC 2851 = 3697 := by
  rw [show (2851:Nat)=2673+(2851-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3788 : CycleSubmission.Artifact.artifact.instructionPC 2852 = 3698 := by
  rw [show (2852:Nat)=2673+(2852-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3789 : CycleSubmission.Artifact.artifact.instructionPC 2853 = 3701 := by
  rw [show (2853:Nat)=2673+(2853-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3790 : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3702 := by
  rw [show (2854:Nat)=2673+(2854-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3791 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3705 := by
  rw [show (2855:Nat)=2673+(2855-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3792 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3706 := by
  rw [show (2856:Nat)=2673+(2856-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3793 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3707 := by
  rw [show (2857:Nat)=2673+(2857-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3794 : CycleSubmission.Artifact.artifact.instructionPC 2858 = 3710 := by
  rw [show (2858:Nat)=2673+(2858-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3795 : CycleSubmission.Artifact.artifact.instructionPC 2859 = 3713 := by
  rw [show (2859:Nat)=2673+(2859-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3796 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3714 := by
  rw [show (2860:Nat)=2673+(2860-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3797 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3715 := by
  rw [show (2861:Nat)=2673+(2861-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3798 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3715 := fixedPC3797

@[simp] theorem fixedPC3799 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3715 := fixedPC3797

@[simp] theorem fixedPC3800 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3716 := by
  rw [show (2862:Nat)=2673+(2862-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3801 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3717 := by
  rw [show (2863:Nat)=2673+(2863-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3802 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3718 := by
  rw [show (2864:Nat)=2673+(2864-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3803 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3721 := by
  rw [show (2865:Nat)=2673+(2865-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3804 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3724 := by
  rw [show (2866:Nat)=2673+(2866-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : CycleSubmission.Artifact.artifact.instructionPC 2709 = 3501 := by
  rw [show (2709:Nat)=2673+(2709-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3115 : CycleSubmission.Artifact.artifact.instructionPC 2710 = 3504 := by
  rw [show (2710:Nat)=2673+(2710-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3116 : CycleSubmission.Artifact.artifact.instructionPC 2711 = 3505 := by
  rw [show (2711:Nat)=2673+(2711-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3117 : CycleSubmission.Artifact.artifact.instructionPC 2712 = 3508 := by
  rw [show (2712:Nat)=2673+(2712-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3118 : CycleSubmission.Artifact.artifact.instructionPC 2713 = 3509 := by
  rw [show (2713:Nat)=2673+(2713-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3119 : CycleSubmission.Artifact.artifact.instructionPC 2714 = 3512 := by
  rw [show (2714:Nat)=2673+(2714-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : CycleSubmission.Artifact.artifact.instructionPC 2681 = 3454 := by
  rw [show (2681:Nat)=2673+(2681-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3462 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3462 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2685 (by rfl)

@[simp] theorem fixedPC3805 : CycleSubmission.Artifact.artifact.instructionPC 2715 = 3513 := by
  rw [show (2715:Nat)=2673+(2715-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3806 : CycleSubmission.Artifact.artifact.instructionPC 2716 = 3515 := by
  rw [show (2716:Nat)=2673+(2716-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3807 : CycleSubmission.Artifact.artifact.instructionPC 2717 = 3516 := by
  rw [show (2717:Nat)=2673+(2717-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3808 : CycleSubmission.Artifact.artifact.instructionPC 2718 = 3519 := by
  rw [show (2718:Nat)=2673+(2718-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPCs8 : CycleSubmission.Artifact.artifact.instructionPC 2719 = 3520 := by
  rw [show (2719:Nat)=2673+(2719-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3809 : CycleSubmission.Artifact.artifact.instructionPC 2720 = 3521 := by
  rw [show (2720:Nat)=2673+(2720-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3810 : CycleSubmission.Artifact.artifact.instructionPC 2721 = 3524 := by
  rw [show (2721:Nat)=2673+(2721-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3811 : CycleSubmission.Artifact.artifact.instructionPC 2722 = 3525 := by
  rw [show (2722:Nat)=2673+(2722-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3812 : CycleSubmission.Artifact.artifact.instructionPC 2723 = 3527 := by
  rw [show (2723:Nat)=2673+(2723-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3813 : CycleSubmission.Artifact.artifact.instructionPC 2724 = 3528 := by
  rw [show (2724:Nat)=2673+(2724-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3814 : CycleSubmission.Artifact.artifact.instructionPC 2725 = 3529 := by
  rw [show (2725:Nat)=2673+(2725-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3815 : CycleSubmission.Artifact.artifact.instructionPC 2726 = 3530 := by
  rw [show (2726:Nat)=2673+(2726-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3816 : CycleSubmission.Artifact.artifact.instructionPC 2726 = 3530 := by
  rw [show (2726:Nat)=2673+(2726-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3817 : CycleSubmission.Artifact.artifact.instructionPC 2727 = 3531 := by
  rw [show (2727:Nat)=2673+(2727-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3818 : CycleSubmission.Artifact.artifact.instructionPC 2728 = 3534 := by
  rw [show (2728:Nat)=2673+(2728-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3819 : CycleSubmission.Artifact.artifact.instructionPC 2729 = 3535 := by
  rw [show (2729:Nat)=2673+(2729-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3820 : CycleSubmission.Artifact.artifact.instructionPC 2730 = 3536 := by
  rw [show (2730:Nat)=2673+(2730-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3821 : CycleSubmission.Artifact.artifact.instructionPC 2731 = 3537 := by
  rw [show (2731:Nat)=2673+(2731-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3822 : CycleSubmission.Artifact.artifact.instructionPC 2732 = 3539 := by
  rw [show (2732:Nat)=2673+(2732-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3823 : CycleSubmission.Artifact.artifact.instructionPC 2733 = 3540 := by
  rw [show (2733:Nat)=2673+(2733-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3824 : CycleSubmission.Artifact.artifact.instructionPC 2734 = 3541 := by
  rw [show (2734:Nat)=2673+(2734-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3825 : CycleSubmission.Artifact.artifact.instructionPC 2735 = 3542 := by
  rw [show (2735:Nat)=2673+(2735-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3826 : CycleSubmission.Artifact.artifact.instructionPC 2736 = 3545 := by
  rw [show (2736:Nat)=2673+(2736-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3827 : CycleSubmission.Artifact.artifact.instructionPC 2737 = 3546 := by
  rw [show (2737:Nat)=2673+(2737-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3828 : CycleSubmission.Artifact.artifact.instructionPC 2738 = 3547 := by
  rw [show (2738:Nat)=2673+(2738-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3829 : CycleSubmission.Artifact.artifact.instructionPC 2739 = 3548 := by
  rw [show (2739:Nat)=2673+(2739-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3830 : CycleSubmission.Artifact.artifact.instructionPC 2740 = 3549 := by
  rw [show (2740:Nat)=2673+(2740-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3831 : CycleSubmission.Artifact.artifact.instructionPC 2741 = 3552 := by
  rw [show (2741:Nat)=2673+(2741-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3832 : CycleSubmission.Artifact.artifact.instructionPC 2742 = 3553 := by
  rw [show (2742:Nat)=2673+(2742-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3833 : CycleSubmission.Artifact.artifact.instructionPC 2743 = 3554 := by
  rw [show (2743:Nat)=2673+(2743-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3834 : CycleSubmission.Artifact.artifact.instructionPC 2743 = 3554 := by
  rw [show (2743:Nat)=2673+(2743-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3835 : CycleSubmission.Artifact.artifact.instructionPC 2744 = 3555 := by
  rw [show (2744:Nat)=2673+(2744-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3836 : CycleSubmission.Artifact.artifact.instructionPC 2745 = 3556 := by
  rw [show (2745:Nat)=2673+(2745-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3837 : CycleSubmission.Artifact.artifact.instructionPC 2746 = 3557 := by
  rw [show (2746:Nat)=2673+(2746-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3838 : CycleSubmission.Artifact.artifact.instructionPC 2747 = 3558 := by
  rw [show (2747:Nat)=2673+(2747-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3839 : CycleSubmission.Artifact.artifact.instructionPC 2748 = 3560 := by
  rw [show (2748:Nat)=2673+(2748-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3840 : CycleSubmission.Artifact.artifact.instructionPC 2749 = 3561 := by
  rw [show (2749:Nat)=2673+(2749-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3841 : CycleSubmission.Artifact.artifact.instructionPC 2750 = 3562 := by
  rw [show (2750:Nat)=2673+(2750-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3842 : CycleSubmission.Artifact.artifact.instructionPC 2751 = 3563 := by
  rw [show (2751:Nat)=2673+(2751-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3843 : CycleSubmission.Artifact.artifact.instructionPC 2752 = 3566 := by
  rw [show (2752:Nat)=2673+(2752-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3844 : CycleSubmission.Artifact.artifact.instructionPC 2753 = 3567 := by
  rw [show (2753:Nat)=2673+(2753-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3845 : CycleSubmission.Artifact.artifact.instructionPC 2754 = 3568 := by
  rw [show (2754:Nat)=2673+(2754-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3846 : CycleSubmission.Artifact.artifact.instructionPC 2755 = 3569 := by
  rw [show (2755:Nat)=2673+(2755-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3847 : CycleSubmission.Artifact.artifact.instructionPC 2756 = 3570 := by
  rw [show (2756:Nat)=2673+(2756-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3848 : CycleSubmission.Artifact.artifact.instructionPC 2757 = 3573 := by
  rw [show (2757:Nat)=2673+(2757-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3849 : CycleSubmission.Artifact.artifact.instructionPC 2758 = 3574 := by
  rw [show (2758:Nat)=2673+(2758-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3850 : CycleSubmission.Artifact.artifact.instructionPC 2759 = 3575 := by
  rw [show (2759:Nat)=2673+(2759-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3851 : CycleSubmission.Artifact.artifact.instructionPC 2760 = 3576 := by
  rw [show (2760:Nat)=2673+(2760-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3852 : CycleSubmission.Artifact.artifact.instructionPC 2760 = 3576 := by
  rw [show (2760:Nat)=2673+(2760-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3853 : CycleSubmission.Artifact.artifact.instructionPC 2761 = 3577 := by
  rw [show (2761:Nat)=2673+(2761-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3854 : CycleSubmission.Artifact.artifact.instructionPC 2762 = 3578 := by
  rw [show (2762:Nat)=2673+(2762-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3855 : CycleSubmission.Artifact.artifact.instructionPC 2763 = 3579 := by
  rw [show (2763:Nat)=2673+(2763-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3856 : CycleSubmission.Artifact.artifact.instructionPC 2764 = 3581 := by
  rw [show (2764:Nat)=2673+(2764-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3857 : CycleSubmission.Artifact.artifact.instructionPC 2765 = 3582 := by
  rw [show (2765:Nat)=2673+(2765-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3858 : CycleSubmission.Artifact.artifact.instructionPC 2766 = 3583 := by
  rw [show (2766:Nat)=2673+(2766-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3859 : CycleSubmission.Artifact.artifact.instructionPC 2767 = 3584 := by
  rw [show (2767:Nat)=2673+(2767-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3860 : CycleSubmission.Artifact.artifact.instructionPC 2768 = 3587 := by
  rw [show (2768:Nat)=2673+(2768-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3861 : CycleSubmission.Artifact.artifact.instructionPC 2769 = 3588 := by
  rw [show (2769:Nat)=2673+(2769-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3862 : CycleSubmission.Artifact.artifact.instructionPC 2770 = 3589 := by
  rw [show (2770:Nat)=2673+(2770-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3863 : CycleSubmission.Artifact.artifact.instructionPC 2771 = 3590 := by
  rw [show (2771:Nat)=2673+(2771-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3864 : CycleSubmission.Artifact.artifact.instructionPC 2772 = 3591 := by
  rw [show (2772:Nat)=2673+(2772-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3865 : CycleSubmission.Artifact.artifact.instructionPC 2773 = 3594 := by
  rw [show (2773:Nat)=2673+(2773-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3866 : CycleSubmission.Artifact.artifact.instructionPC 2774 = 3595 := by
  rw [show (2774:Nat)=2673+(2774-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3867 : CycleSubmission.Artifact.artifact.instructionPC 2775 = 3596 := by
  rw [show (2775:Nat)=2673+(2775-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3868 : CycleSubmission.Artifact.artifact.instructionPC 2776 = 3597 := by
  rw [show (2776:Nat)=2673+(2776-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3869 : CycleSubmission.Artifact.artifact.instructionPC 2777 = 3598 := by
  rw [show (2777:Nat)=2673+(2777-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3871 : CycleSubmission.Artifact.artifact.instructionPC 2777 = 3598 := by
  rw [show (2777:Nat)=2673+(2777-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3872 : CycleSubmission.Artifact.artifact.instructionPC 2778 = 3599 := by
  rw [show (2778:Nat)=2673+(2778-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3873 : CycleSubmission.Artifact.artifact.instructionPC 2779 = 3600 := by
  rw [show (2779:Nat)=2673+(2779-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3874 : CycleSubmission.Artifact.artifact.instructionPC 2780 = 3602 := by
  rw [show (2780:Nat)=2673+(2780-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3875 : CycleSubmission.Artifact.artifact.instructionPC 2781 = 3603 := by
  rw [show (2781:Nat)=2673+(2781-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3876 : CycleSubmission.Artifact.artifact.instructionPC 2782 = 3604 := by
  rw [show (2782:Nat)=2673+(2782-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3877 : CycleSubmission.Artifact.artifact.instructionPC 2783 = 3605 := by
  rw [show (2783:Nat)=2673+(2783-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3878 : CycleSubmission.Artifact.artifact.instructionPC 2784 = 3608 := by
  rw [show (2784:Nat)=2673+(2784-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3879 : CycleSubmission.Artifact.artifact.instructionPC 2785 = 3609 := by
  rw [show (2785:Nat)=2673+(2785-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3880 : CycleSubmission.Artifact.artifact.instructionPC 2786 = 3610 := by
  rw [show (2786:Nat)=2673+(2786-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3881 : CycleSubmission.Artifact.artifact.instructionPC 2787 = 3611 := by
  rw [show (2787:Nat)=2673+(2787-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3882 : CycleSubmission.Artifact.artifact.instructionPC 2788 = 3612 := by
  rw [show (2788:Nat)=2673+(2788-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3883 : CycleSubmission.Artifact.artifact.instructionPC 2789 = 3615 := by
  rw [show (2789:Nat)=2673+(2789-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3884 : CycleSubmission.Artifact.artifact.instructionPC 2790 = 3616 := by
  rw [show (2790:Nat)=2673+(2790-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3885 : CycleSubmission.Artifact.artifact.instructionPC 2791 = 3617 := by
  rw [show (2791:Nat)=2673+(2791-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3886 : CycleSubmission.Artifact.artifact.instructionPC 2792 = 3618 := by
  rw [show (2792:Nat)=2673+(2792-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3887 : CycleSubmission.Artifact.artifact.instructionPC 2793 = 3619 := by
  rw [show (2793:Nat)=2673+(2793-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3888 : CycleSubmission.Artifact.artifact.instructionPC 2794 = 3620 := by
  rw [show (2794:Nat)=2673+(2794-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3889 : CycleSubmission.Artifact.artifact.instructionPC 2794 = 3620 := by
  rw [show (2794:Nat)=2673+(2794-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3620 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2794 = 3620 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2794 (by rfl)

@[simp] theorem fixedPC3890 : CycleSubmission.Artifact.artifact.instructionPC 2795 = 3621 := by
  rw [show (2795:Nat)=2673+(2795-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3891 : CycleSubmission.Artifact.artifact.instructionPC 2796 = 3622 := by
  rw [show (2796:Nat)=2673+(2796-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3892 : CycleSubmission.Artifact.artifact.instructionPC 2797 = 3624 := by
  rw [show (2797:Nat)=2673+(2797-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3893 : CycleSubmission.Artifact.artifact.instructionPC 2798 = 3625 := by
  rw [show (2798:Nat)=2673+(2798-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3894 : CycleSubmission.Artifact.artifact.instructionPC 2799 = 3626 := by
  rw [show (2799:Nat)=2673+(2799-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3895 : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3627 := by
  rw [show (2800:Nat)=2673+(2800-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3896 : CycleSubmission.Artifact.artifact.instructionPC 2801 = 3630 := by
  rw [show (2801:Nat)=2673+(2801-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3897 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3631 := by
  rw [show (2802:Nat)=2673+(2802-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3898 : CycleSubmission.Artifact.artifact.instructionPC 2803 = 3632 := by
  rw [show (2803:Nat)=2673+(2803-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3899 : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3633 := by
  rw [show (2804:Nat)=2673+(2804-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3900 : CycleSubmission.Artifact.artifact.instructionPC 2805 = 3634 := by
  rw [show (2805:Nat)=2673+(2805-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3901 : CycleSubmission.Artifact.artifact.instructionPC 2806 = 3637 := by
  rw [show (2806:Nat)=2673+(2806-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3902 : CycleSubmission.Artifact.artifact.instructionPC 2807 = 3638 := by
  rw [show (2807:Nat)=2673+(2807-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3903 : CycleSubmission.Artifact.artifact.instructionPC 2808 = 3639 := by
  rw [show (2808:Nat)=2673+(2808-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3904 : CycleSubmission.Artifact.artifact.instructionPC 2809 = 3640 := by
  rw [show (2809:Nat)=2673+(2809-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3905 : CycleSubmission.Artifact.artifact.instructionPC 2810 = 3641 := by
  rw [show (2810:Nat)=2673+(2810-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3906 : CycleSubmission.Artifact.artifact.instructionPC 2811 = 3642 := by
  rw [show (2811:Nat)=2673+(2811-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3907 : CycleSubmission.Artifact.artifact.instructionPC 2812 = 3643 := by
  rw [show (2812:Nat)=2673+(2812-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3908 : CycleSubmission.Artifact.artifact.instructionPC 2812 = 3643 := by
  rw [show (2812:Nat)=2673+(2812-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3909 : CycleSubmission.Artifact.artifact.instructionPC 2813 = 3645 := by
  rw [show (2813:Nat)=2673+(2813-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3910 : CycleSubmission.Artifact.artifact.instructionPC 2814 = 3646 := by
  rw [show (2814:Nat)=2673+(2814-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3911 : CycleSubmission.Artifact.artifact.instructionPC 2815 = 3647 := by
  rw [show (2815:Nat)=2673+(2815-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3912 : CycleSubmission.Artifact.artifact.instructionPC 2816 = 3648 := by
  rw [show (2816:Nat)=2673+(2816-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3913 : CycleSubmission.Artifact.artifact.instructionPC 2817 = 3651 := by
  rw [show (2817:Nat)=2673+(2817-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3914 : CycleSubmission.Artifact.artifact.instructionPC 2818 = 3652 := by
  rw [show (2818:Nat)=2673+(2818-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3915 : CycleSubmission.Artifact.artifact.instructionPC 2819 = 3653 := by
  rw [show (2819:Nat)=2673+(2819-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3916 : CycleSubmission.Artifact.artifact.instructionPC 2820 = 3654 := by
  rw [show (2820:Nat)=2673+(2820-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3917 : CycleSubmission.Artifact.artifact.instructionPC 2821 = 3655 := by
  rw [show (2821:Nat)=2673+(2821-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3918 : CycleSubmission.Artifact.artifact.instructionPC 2822 = 3658 := by
  rw [show (2822:Nat)=2673+(2822-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3919 : CycleSubmission.Artifact.artifact.instructionPC 2823 = 3659 := by
  rw [show (2823:Nat)=2673+(2823-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3920 : CycleSubmission.Artifact.artifact.instructionPC 2824 = 3660 := by
  rw [show (2824:Nat)=2673+(2824-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2825 = 3661 := by
  rw [show (2825:Nat)=2673+(2825-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2826 = 3662 := by
  rw [show (2826:Nat)=2673+(2826-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2827 = 3663 := by
  rw [show (2827:Nat)=2673+(2827-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2828 = 3664 := by
  rw [show (2828:Nat)=2673+(2828-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2829 = 3665 := by
  rw [show (2829:Nat)=2673+(2829-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2829 = 3665 := by
  rw [show (2829:Nat)=2673+(2829-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2830 = 3666 := by
  rw [show (2830:Nat)=2673+(2830-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2831 = 3667 := by
  rw [show (2831:Nat)=2673+(2831-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3929 : CycleSubmission.Artifact.artifact.instructionPC 2832 = 3668 := by
  rw [show (2832:Nat)=2673+(2832-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3930 : CycleSubmission.Artifact.artifact.instructionPC 2833 = 3671 := by
  rw [show (2833:Nat)=2673+(2833-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3931 : CycleSubmission.Artifact.artifact.instructionPC 2834 = 3672 := by
  rw [show (2834:Nat)=2673+(2834-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3932 : CycleSubmission.Artifact.artifact.instructionPC 2835 = 3673 := by
  rw [show (2835:Nat)=2673+(2835-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3933 : CycleSubmission.Artifact.artifact.instructionPC 2836 = 3674 := by
  rw [show (2836:Nat)=2673+(2836-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3934 : CycleSubmission.Artifact.artifact.instructionPC 2837 = 3675 := by
  rw [show (2837:Nat)=2673+(2837-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3935 : CycleSubmission.Artifact.artifact.instructionPC 2838 = 3678 := by
  rw [show (2838:Nat)=2673+(2838-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3936 : CycleSubmission.Artifact.artifact.instructionPC 2839 = 3679 := by
  rw [show (2839:Nat)=2673+(2839-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3937 : CycleSubmission.Artifact.artifact.instructionPC 2840 = 3680 := by
  rw [show (2840:Nat)=2673+(2840-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3938 : CycleSubmission.Artifact.artifact.instructionPC 2841 = 3681 := by
  rw [show (2841:Nat)=2673+(2841-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3939 : CycleSubmission.Artifact.artifact.instructionPC 2842 = 3682 := by
  rw [show (2842:Nat)=2673+(2842-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3940 : CycleSubmission.Artifact.artifact.instructionPC 2843 = 3683 := by
  rw [show (2843:Nat)=2673+(2843-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3941 : CycleSubmission.Artifact.artifact.instructionPC 2844 = 3684 := by
  rw [show (2844:Nat)=2673+(2844-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3942 : CycleSubmission.Artifact.artifact.instructionPC 2845 = 3687 := by
  rw [show (2845:Nat)=2673+(2845-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3943 : CycleSubmission.Artifact.artifact.instructionPC 2846 = 3688 := by
  rw [show (2846:Nat)=2673+(2846-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3944 : CycleSubmission.Artifact.artifact.instructionPC 2846 = 3688 := by
  rw [show (2846:Nat)=2673+(2846-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3945 : CycleSubmission.Artifact.artifact.instructionPC 2847 = 3689 := by
  rw [show (2847:Nat)=2673+(2847-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3946 : CycleSubmission.Artifact.artifact.instructionPC 2848 = 3692 := by
  rw [show (2848:Nat)=2673+(2848-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3947 : CycleSubmission.Artifact.artifact.instructionPC 2849 = 3693 := by
  rw [show (2849:Nat)=2673+(2849-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3948 : CycleSubmission.Artifact.artifact.instructionPC 2850 = 3696 := by
  rw [show (2850:Nat)=2673+(2850-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3949 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3714 := by
  rw [show (2860:Nat)=2673+(2860-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3950 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3714 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3715 := by
  rw [show (2861:Nat)=2673+(2861-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3952 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3716 := by
  rw [show (2862:Nat)=2673+(2862-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3953 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3717 := by
  rw [show (2863:Nat)=2673+(2863-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3954 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3718 := by
  rw [show (2864:Nat)=2673+(2864-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3955 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3721 := by
  rw [show (2865:Nat)=2673+(2865-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3956 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3724 := by
  rw [show (2866:Nat)=2673+(2866-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3957 : CycleSubmission.Artifact.artifact.instructionPC 2867 = 3725 := by
  rw [show (2867:Nat)=2673+(2867-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4190 : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3477 := by
  rw [show (2695:Nat)=2673+(2695-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4193 : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3478 := by
  rw [show (2696:Nat)=2673+(2696-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4194 : CycleSubmission.Artifact.artifact.instructionPC 2697 = 3481 := by
  rw [show (2697:Nat)=2673+(2697-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4547 : CycleSubmission.Artifact.artifact.instructionPC 2868 = 3726 := by
  rw [show (2868:Nat)=2673+(2868-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4548 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3727 := by
  rw [show (2869:Nat)=2673+(2869-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC3999 : CycleSubmission.Artifact.artifact.instructionPC 2681 = 3454 := by
  rw [show (2681:Nat)=2673+(2681-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3462 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3462 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2685 (by rfl)

@[simp] theorem fixedPC4000 : CycleSubmission.Artifact.artifact.instructionPC 2682 = 3457 := by
  rw [show (2682:Nat)=2673+(2682-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4001 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3458 := by
  rw [show (2683:Nat)=2673+(2683-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4002 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3461 := by
  rw [show (2684:Nat)=2673+(2684-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4003 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3462 := by
  rw [show (2685:Nat)=2673+(2685-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4004 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3463 := by
  rw [show (2686:Nat)=2673+(2686-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4005 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3466 := by
  rw [show (2687:Nat)=2673+(2687-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4006 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3467 := by
  rw [show (2688:Nat)=2673+(2688-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4007 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3469 := by
  rw [show (2689:Nat)=2673+(2689-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4008 : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3470 := by
  rw [show (2690:Nat)=2673+(2690-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4009 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3471 := by
  rw [show (2691:Nat)=2673+(2691-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4010 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3472 := by
  rw [show (2692:Nat)=2673+(2692-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4011 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3473 := by
  rw [show (2693:Nat)=2673+(2693-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4012 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3476 := by
  rw [show (2694:Nat)=2673+(2694-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2883 : CycleSubmission.Artifact.artifact.instructionPC 2669 = 3438 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : CycleSubmission.Artifact.artifact.instructionPC 2670 = 3439 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : CycleSubmission.Artifact.artifact.instructionPC 2671 = 3440 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : CycleSubmission.Artifact.artifact.instructionPC 2672 = 3441 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : CycleSubmission.Artifact.artifact.instructionPC 2673 = 3442 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : CycleSubmission.Artifact.artifact.instructionPC 2674 = 3443 := by
  rw [show (2674:Nat)=2673+(2674-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2890 : CycleSubmission.Artifact.artifact.instructionPC 2675 = 3444 := by
  rw [show (2675:Nat)=2673+(2675-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2891 : CycleSubmission.Artifact.artifact.instructionPC 2676 = 3447 := by
  rw [show (2676:Nat)=2673+(2676-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2892 : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3448 := by
  rw [show (2677:Nat)=2673+(2677-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2893 : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3448 := by
  rw [show (2677:Nat)=2673+(2677-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2894 : CycleSubmission.Artifact.artifact.instructionPC 2678 = 3449 := by
  rw [show (2678:Nat)=2673+(2678-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2895 : CycleSubmission.Artifact.artifact.instructionPC 2679 = 3452 := by
  rw [show (2679:Nat)=2673+(2679-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2896 : CycleSubmission.Artifact.artifact.instructionPC 2680 = 3453 := by
  rw [show (2680:Nat)=2673+(2680-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2930 : CycleSubmission.Artifact.artifact.instructionPC 2681 = 3454 := by
  rw [show (2681:Nat)=2673+(2681-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2931 : CycleSubmission.Artifact.artifact.instructionPC 2682 = 3457 := by
  rw [show (2682:Nat)=2673+(2682-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2932 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3458 := by
  rw [show (2683:Nat)=2673+(2683-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2933 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3461 := by
  rw [show (2684:Nat)=2673+(2684-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2934 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3462 := by
  rw [show (2685:Nat)=2673+(2685-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2935 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3463 := by
  rw [show (2686:Nat)=2673+(2686-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2936 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3466 := by
  rw [show (2687:Nat)=2673+(2687-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2937 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3467 := by
  rw [show (2688:Nat)=2673+(2688-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2938 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3469 := by
  rw [show (2689:Nat)=2673+(2689-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2939 : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3470 := by
  rw [show (2690:Nat)=2673+(2690-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2940 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3471 := by
  rw [show (2691:Nat)=2673+(2691-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2941 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3472 := by
  rw [show (2692:Nat)=2673+(2692-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2942 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3473 := by
  rw [show (2693:Nat)=2673+(2693-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2943 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3476 := by
  rw [show (2694:Nat)=2673+(2694-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2852 = 3698 := by
  rw [show (2852:Nat)=2673+(2852-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2853 = 3701 := by
  rw [show (2853:Nat)=2673+(2853-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3702 := by
  rw [show (2854:Nat)=2673+(2854-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3705 := by
  rw [show (2855:Nat)=2673+(2855-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3706 := by
  rw [show (2856:Nat)=2673+(2856-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3707 := by
  rw [show (2857:Nat)=2673+(2857-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2858 = 3710 := by
  rw [show (2858:Nat)=2673+(2858-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2859 = 3713 := by
  rw [show (2859:Nat)=2673+(2859-2673) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

end CycleSubmission.Global.Fast
