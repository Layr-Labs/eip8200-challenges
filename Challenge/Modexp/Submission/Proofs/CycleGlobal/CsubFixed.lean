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
  [pushAt 2711 2 2688,
   opAt 2712 .MLOAD,
   pushAt 2713 1 128,
   opAt 2714 .EQ,
   pushAt 2715 2 3462,
   opAt 2716 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2711 2 2688,
   opAt 2712 .MLOAD,
   pushAt 2713 1 128,
   opAt 2714 .EQ,
   pushAt 2715 2 3462,
   opAt 2716 .JUMPI,
   opAt 2677 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2717 .JUMPDEST,
   pushAt 2718 2 2336,
   opAt 2719 .MLOAD,
   pushAt 2720 1 224,
   opAt 2721 .MLOAD,
   opAt 2722 (.Dup ⟨0, by decide⟩),
   opAt 2723 (.Dup ⟨2, by decide⟩),
   opAt 2724 .SUB,
   pushAt 2725 2 2016,
   opAt 2726 .MSTORE,
   opAt 2727 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2728 (.Dup ⟨0, by decide⟩),
   pushAt 2729 1 192,
   opAt 2730 .MLOAD,
   opAt 2731 .ADD,
   opAt 2732 (.Dup ⟨0, by decide⟩),
   pushAt 2733 2 2304,
   opAt 2734 .MLOAD,
   opAt 2735 (.Dup ⟨1, by decide⟩),
   opAt 2736 (.Dup ⟨1, by decide⟩),
   opAt 2737 .SUB,
   pushAt 2738 2 1984,
   opAt 2739 .MSTORE,
   opAt 2740 .LT,
   opAt 2741 (.Swap ⟨1, by decide⟩),
   opAt 2742 .GT,
   opAt 2743 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2744 (.Dup ⟨0, by decide⟩),
   pushAt 2745 1 160,
   opAt 2746 .MLOAD,
   opAt 2747 .ADD,
   opAt 2748 (.Dup ⟨0, by decide⟩),
   pushAt 2749 2 2272,
   opAt 2750 .MLOAD,
   opAt 2751 (.Dup ⟨1, by decide⟩),
   opAt 2752 (.Dup ⟨1, by decide⟩),
   opAt 2753 .SUB,
   pushAt 2754 2 1952,
   opAt 2755 .MSTORE,
   opAt 2756 .LT,
   opAt 2757 (.Swap ⟨1, by decide⟩),
   opAt 2758 .GT,
   opAt 2759 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2760 (.Dup ⟨0, by decide⟩),
   pushAt 2761 1 128,
   opAt 2762 .MLOAD,
   opAt 2763 .ADD,
   opAt 2764 (.Dup ⟨0, by decide⟩),
   pushAt 2765 2 2240,
   opAt 2766 .MLOAD,
   opAt 2767 (.Dup ⟨1, by decide⟩),
   opAt 2768 (.Dup ⟨1, by decide⟩),
   opAt 2769 .SUB,
   pushAt 2770 2 1920,
   opAt 2771 .MSTORE,
   opAt 2772 .LT,
   opAt 2773 (.Swap ⟨1, by decide⟩),
   opAt 2774 .GT,
   opAt 2775 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2776 (.Dup ⟨0, by decide⟩),
   pushAt 2777 1 96,
   opAt 2778 .MLOAD,
   opAt 2779 .ADD,
   opAt 2780 (.Dup ⟨0, by decide⟩),
   pushAt 2781 2 2208,
   opAt 2782 .MLOAD,
   opAt 2783 (.Dup ⟨1, by decide⟩),
   opAt 2784 (.Dup ⟨1, by decide⟩),
   opAt 2785 .SUB,
   pushAt 2786 2 1888,
   opAt 2787 .MSTORE,
   opAt 2788 .LT,
   opAt 2789 (.Swap ⟨1, by decide⟩),
   opAt 2790 .GT,
   opAt 2791 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2792 .JUMPDEST,
   opAt 2793 (.Dup ⟨0, by decide⟩),
   pushAt 2794 1 64,
   opAt 2795 .MLOAD,
   opAt 2796 .ADD,
   opAt 2797 (.Dup ⟨0, by decide⟩),
   pushAt 2798 2 2176,
   opAt 2799 .MLOAD,
   opAt 2800 (.Dup ⟨1, by decide⟩),
   opAt 2801 (.Dup ⟨1, by decide⟩),
   opAt 2802 .SUB,
   pushAt 2803 2 1856,
   opAt 2804 .MSTORE,
   opAt 2805 .LT,
   opAt 2806 (.Swap ⟨1, by decide⟩),
   opAt 2807 .GT,
   opAt 2808 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2809 (.Dup ⟨0, by decide⟩),
   pushAt 2810 1 32,
   opAt 2811 .MLOAD,
   opAt 2812 .ADD,
   opAt 2813 (.Dup ⟨0, by decide⟩),
   pushAt 2814 2 2144,
   opAt 2815 .MLOAD,
   opAt 2816 (.Dup ⟨1, by decide⟩),
   opAt 2817 (.Dup ⟨1, by decide⟩),
   opAt 2818 .SUB,
   pushAt 2819 2 1824,
   opAt 2820 .MSTORE,
   opAt 2821 .LT,
   opAt 2822 (.Swap ⟨1, by decide⟩),
   opAt 2823 .GT,
   opAt 2824 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2825 (.Dup ⟨0, by decide⟩),
   pushAt 2826 0 0,
   opAt 2827 .MLOAD,
   opAt 2828 .ADD,
   opAt 2829 (.Dup ⟨0, by decide⟩),
   pushAt 2830 2 2112,
   opAt 2831 .MLOAD,
   opAt 2832 (.Dup ⟨1, by decide⟩),
   opAt 2833 (.Dup ⟨1, by decide⟩),
   opAt 2834 .SUB,
   pushAt 2835 2 1792,
   opAt 2836 .MSTORE,
   opAt 2837 .LT,
   opAt 2838 (.Swap ⟨1, by decide⟩),
   opAt 2839 .GT,
   opAt 2840 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2841 .ISZERO,
   pushAt 2842 2 2080,
   opAt 2843 .MLOAD,
   opAt 2844 .OR,
   pushAt 2845 2 3717,
   opAt 2846 .JUMPI,
   opAt 2865 .JUMPDEST,
   pushAt 2866 2 1792,
   pushAt 2867 2 2688,
   opAt 2868 .MLOAD,
   opAt 2869 (.Swap ⟨1, by decide⟩),
   opAt 2870 .MCOPY,
   opAt 2871 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2841 .ISZERO,
   pushAt 2842 2 2080,
   opAt 2843 .MLOAD,
   opAt 2844 .OR,
   pushAt 2845 2 3717,
   opAt 2846 .JUMPI,
   pushAt 2847 2 3706,
   opAt 2848 .JUMP,
   opAt 2858 .JUMPDEST,
   pushAt 2859 2 2112,
   pushAt 2860 2 2688,
   opAt 2861 .MLOAD,
   opAt 2862 (.Swap ⟨1, by decide⟩),
   opAt 2863 .MCOPY,
   opAt 2864 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2678 2 2208,
   opAt 2679 .MLOAD,
   pushAt 2680 1 96,
   opAt 2681 .MLOAD,
   opAt 2682 (.Dup ⟨0, by decide⟩),
   opAt 2683 (.Dup ⟨2, by decide⟩),
   opAt 2684 .SUB,
   pushAt 2685 2 1888,
   opAt 2686 .MSTORE,
   opAt 2687 .GT,
   pushAt 2688 2 3620,
   opAt 2689 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2792 .JUMPDEST,
   opAt 2793 (.Dup ⟨0, by decide⟩),
   pushAt 2794 1 64,
   opAt 2795 .MLOAD,
   opAt 2796 .ADD,
   opAt 2797 (.Dup ⟨0, by decide⟩),
   pushAt 2798 2 2176,
   opAt 2799 .MLOAD,
   opAt 2800 (.Dup ⟨1, by decide⟩),
   opAt 2801 (.Dup ⟨1, by decide⟩),
   opAt 2802 .SUB,
   pushAt 2803 2 1856,
   opAt 2804 .MSTORE,
   opAt 2805 .LT,
   opAt 2806 (.Swap ⟨1, by decide⟩),
   opAt 2807 .GT,
   opAt 2808 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2809 (.Dup ⟨0, by decide⟩),
   pushAt 2810 1 32,
   opAt 2811 .MLOAD,
   opAt 2812 .ADD,
   opAt 2813 (.Dup ⟨0, by decide⟩),
   pushAt 2814 2 2144,
   opAt 2815 .MLOAD,
   opAt 2816 (.Dup ⟨1, by decide⟩),
   opAt 2817 (.Dup ⟨1, by decide⟩),
   opAt 2818 .SUB,
   pushAt 2819 2 1824,
   opAt 2820 .MSTORE,
   opAt 2821 .LT,
   opAt 2822 (.Swap ⟨1, by decide⟩),
   opAt 2823 .GT,
   opAt 2824 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2825 (.Dup ⟨0, by decide⟩),
   pushAt 2826 0 0,
   opAt 2827 .MLOAD,
   opAt 2828 .ADD,
   opAt 2829 (.Dup ⟨0, by decide⟩),
   pushAt 2830 2 2112,
   opAt 2831 .MLOAD,
   opAt 2832 (.Dup ⟨1, by decide⟩),
   opAt 2833 (.Dup ⟨1, by decide⟩),
   opAt 2834 .SUB,
   pushAt 2835 2 1792,
   opAt 2836 .MSTORE,
   opAt 2837 .LT,
   opAt 2838 (.Swap ⟨1, by decide⟩),
   opAt 2839 .GT,
   opAt 2840 .OR]

private theorem cycleAnchor : CycleSubmission.Artifact.artifact.instructionPC 2662 = 3447 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem fixedPC3777 : CycleSubmission.Artifact.artifact.instructionPC 2706 = 3500 := by
  rw [show (2706:Nat)=2662+(2706-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3778 : CycleSubmission.Artifact.artifact.instructionPC 2847 = 3693 := by
  rw [show (2847:Nat)=2662+(2847-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3779 : CycleSubmission.Artifact.artifact.instructionPC 2848 = 3696 := by
  rw [show (2848:Nat)=2662+(2848-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3787 : CycleSubmission.Artifact.artifact.instructionPC 2849 = 3697 := by
  rw [show (2849:Nat)=2662+(2849-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3788 : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3702 := by
  rw [show (2854:Nat)=2662+(2854-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3789 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3703 := by
  rw [show (2855:Nat)=2662+(2855-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3790 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3704 := by
  rw [show (2856:Nat)=2662+(2856-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3791 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3705 := by
  rw [show (2857:Nat)=2662+(2857-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3792 : CycleSubmission.Artifact.artifact.instructionPC 2858 = 3706 := by
  rw [show (2858:Nat)=2662+(2858-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3793 : CycleSubmission.Artifact.artifact.instructionPC 2859 = 3707 := by
  rw [show (2859:Nat)=2662+(2859-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3794 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3710 := by
  rw [show (2860:Nat)=2662+(2860-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3795 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3713 := by
  rw [show (2861:Nat)=2662+(2861-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3796 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3714 := by
  rw [show (2862:Nat)=2662+(2862-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3797 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3715 := by
  rw [show (2863:Nat)=2662+(2863-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3798 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3715 := fixedPC3797

@[simp] theorem fixedPC3799 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3715 := fixedPC3797

@[simp] theorem fixedPC3800 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3716 := by
  rw [show (2864:Nat)=2662+(2864-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3801 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3717 := by
  rw [show (2865:Nat)=2662+(2865-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3802 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3718 := by
  rw [show (2866:Nat)=2662+(2866-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3803 : CycleSubmission.Artifact.artifact.instructionPC 2867 = 3721 := by
  rw [show (2867:Nat)=2662+(2867-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3804 : CycleSubmission.Artifact.artifact.instructionPC 2868 = 3724 := by
  rw [show (2868:Nat)=2662+(2868-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : CycleSubmission.Artifact.artifact.instructionPC 2707 = 3501 := by
  rw [show (2707:Nat)=2662+(2707-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3115 : CycleSubmission.Artifact.artifact.instructionPC 2708 = 3502 := by
  rw [show (2708:Nat)=2662+(2708-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3116 : CycleSubmission.Artifact.artifact.instructionPC 2709 = 3503 := by
  rw [show (2709:Nat)=2662+(2709-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3117 : CycleSubmission.Artifact.artifact.instructionPC 2710 = 3506 := by
  rw [show (2710:Nat)=2662+(2710-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3118 : CycleSubmission.Artifact.artifact.instructionPC 2711 = 3509 := by
  rw [show (2711:Nat)=2662+(2711-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3119 : CycleSubmission.Artifact.artifact.instructionPC 2712 = 3512 := by
  rw [show (2712:Nat)=2662+(2712-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : CycleSubmission.Artifact.artifact.instructionPC 2673 = 3458 := by
  rw [show (2673:Nat)=2662+(2673-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3462 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3462 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2677 (by rfl)

@[simp] theorem fixedPC3805 : CycleSubmission.Artifact.artifact.instructionPC 2713 = 3513 := by
  rw [show (2713:Nat)=2662+(2713-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3806 : CycleSubmission.Artifact.artifact.instructionPC 2714 = 3515 := by
  rw [show (2714:Nat)=2662+(2714-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3807 : CycleSubmission.Artifact.artifact.instructionPC 2715 = 3516 := by
  rw [show (2715:Nat)=2662+(2715-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3808 : CycleSubmission.Artifact.artifact.instructionPC 2716 = 3519 := by
  rw [show (2716:Nat)=2662+(2716-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPCs8 : CycleSubmission.Artifact.artifact.instructionPC 2717 = 3520 := by
  rw [show (2717:Nat)=2662+(2717-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3809 : CycleSubmission.Artifact.artifact.instructionPC 2718 = 3521 := by
  rw [show (2718:Nat)=2662+(2718-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3810 : CycleSubmission.Artifact.artifact.instructionPC 2719 = 3524 := by
  rw [show (2719:Nat)=2662+(2719-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3811 : CycleSubmission.Artifact.artifact.instructionPC 2720 = 3525 := by
  rw [show (2720:Nat)=2662+(2720-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3812 : CycleSubmission.Artifact.artifact.instructionPC 2721 = 3527 := by
  rw [show (2721:Nat)=2662+(2721-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3813 : CycleSubmission.Artifact.artifact.instructionPC 2722 = 3528 := by
  rw [show (2722:Nat)=2662+(2722-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3814 : CycleSubmission.Artifact.artifact.instructionPC 2723 = 3529 := by
  rw [show (2723:Nat)=2662+(2723-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3815 : CycleSubmission.Artifact.artifact.instructionPC 2724 = 3530 := by
  rw [show (2724:Nat)=2662+(2724-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3816 : CycleSubmission.Artifact.artifact.instructionPC 2724 = 3530 := by
  rw [show (2724:Nat)=2662+(2724-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3817 : CycleSubmission.Artifact.artifact.instructionPC 2725 = 3531 := by
  rw [show (2725:Nat)=2662+(2725-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3818 : CycleSubmission.Artifact.artifact.instructionPC 2726 = 3534 := by
  rw [show (2726:Nat)=2662+(2726-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3819 : CycleSubmission.Artifact.artifact.instructionPC 2727 = 3535 := by
  rw [show (2727:Nat)=2662+(2727-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3820 : CycleSubmission.Artifact.artifact.instructionPC 2728 = 3536 := by
  rw [show (2728:Nat)=2662+(2728-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3821 : CycleSubmission.Artifact.artifact.instructionPC 2729 = 3537 := by
  rw [show (2729:Nat)=2662+(2729-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3822 : CycleSubmission.Artifact.artifact.instructionPC 2730 = 3539 := by
  rw [show (2730:Nat)=2662+(2730-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3823 : CycleSubmission.Artifact.artifact.instructionPC 2731 = 3540 := by
  rw [show (2731:Nat)=2662+(2731-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3824 : CycleSubmission.Artifact.artifact.instructionPC 2732 = 3541 := by
  rw [show (2732:Nat)=2662+(2732-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3825 : CycleSubmission.Artifact.artifact.instructionPC 2733 = 3542 := by
  rw [show (2733:Nat)=2662+(2733-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3826 : CycleSubmission.Artifact.artifact.instructionPC 2734 = 3545 := by
  rw [show (2734:Nat)=2662+(2734-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3827 : CycleSubmission.Artifact.artifact.instructionPC 2735 = 3546 := by
  rw [show (2735:Nat)=2662+(2735-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3828 : CycleSubmission.Artifact.artifact.instructionPC 2736 = 3547 := by
  rw [show (2736:Nat)=2662+(2736-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3829 : CycleSubmission.Artifact.artifact.instructionPC 2737 = 3548 := by
  rw [show (2737:Nat)=2662+(2737-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3830 : CycleSubmission.Artifact.artifact.instructionPC 2738 = 3549 := by
  rw [show (2738:Nat)=2662+(2738-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3831 : CycleSubmission.Artifact.artifact.instructionPC 2739 = 3552 := by
  rw [show (2739:Nat)=2662+(2739-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3832 : CycleSubmission.Artifact.artifact.instructionPC 2740 = 3553 := by
  rw [show (2740:Nat)=2662+(2740-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3833 : CycleSubmission.Artifact.artifact.instructionPC 2741 = 3554 := by
  rw [show (2741:Nat)=2662+(2741-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3834 : CycleSubmission.Artifact.artifact.instructionPC 2741 = 3554 := by
  rw [show (2741:Nat)=2662+(2741-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3835 : CycleSubmission.Artifact.artifact.instructionPC 2742 = 3555 := by
  rw [show (2742:Nat)=2662+(2742-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3836 : CycleSubmission.Artifact.artifact.instructionPC 2743 = 3556 := by
  rw [show (2743:Nat)=2662+(2743-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3837 : CycleSubmission.Artifact.artifact.instructionPC 2744 = 3557 := by
  rw [show (2744:Nat)=2662+(2744-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3838 : CycleSubmission.Artifact.artifact.instructionPC 2745 = 3558 := by
  rw [show (2745:Nat)=2662+(2745-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3839 : CycleSubmission.Artifact.artifact.instructionPC 2746 = 3560 := by
  rw [show (2746:Nat)=2662+(2746-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3840 : CycleSubmission.Artifact.artifact.instructionPC 2747 = 3561 := by
  rw [show (2747:Nat)=2662+(2747-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3841 : CycleSubmission.Artifact.artifact.instructionPC 2748 = 3562 := by
  rw [show (2748:Nat)=2662+(2748-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3842 : CycleSubmission.Artifact.artifact.instructionPC 2749 = 3563 := by
  rw [show (2749:Nat)=2662+(2749-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3843 : CycleSubmission.Artifact.artifact.instructionPC 2750 = 3566 := by
  rw [show (2750:Nat)=2662+(2750-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3844 : CycleSubmission.Artifact.artifact.instructionPC 2751 = 3567 := by
  rw [show (2751:Nat)=2662+(2751-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3845 : CycleSubmission.Artifact.artifact.instructionPC 2752 = 3568 := by
  rw [show (2752:Nat)=2662+(2752-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3846 : CycleSubmission.Artifact.artifact.instructionPC 2753 = 3569 := by
  rw [show (2753:Nat)=2662+(2753-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3847 : CycleSubmission.Artifact.artifact.instructionPC 2754 = 3570 := by
  rw [show (2754:Nat)=2662+(2754-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3848 : CycleSubmission.Artifact.artifact.instructionPC 2755 = 3573 := by
  rw [show (2755:Nat)=2662+(2755-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3849 : CycleSubmission.Artifact.artifact.instructionPC 2756 = 3574 := by
  rw [show (2756:Nat)=2662+(2756-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3850 : CycleSubmission.Artifact.artifact.instructionPC 2757 = 3575 := by
  rw [show (2757:Nat)=2662+(2757-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3851 : CycleSubmission.Artifact.artifact.instructionPC 2758 = 3576 := by
  rw [show (2758:Nat)=2662+(2758-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3852 : CycleSubmission.Artifact.artifact.instructionPC 2758 = 3576 := by
  rw [show (2758:Nat)=2662+(2758-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3853 : CycleSubmission.Artifact.artifact.instructionPC 2759 = 3577 := by
  rw [show (2759:Nat)=2662+(2759-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3854 : CycleSubmission.Artifact.artifact.instructionPC 2760 = 3578 := by
  rw [show (2760:Nat)=2662+(2760-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3855 : CycleSubmission.Artifact.artifact.instructionPC 2761 = 3579 := by
  rw [show (2761:Nat)=2662+(2761-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3856 : CycleSubmission.Artifact.artifact.instructionPC 2762 = 3581 := by
  rw [show (2762:Nat)=2662+(2762-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3857 : CycleSubmission.Artifact.artifact.instructionPC 2763 = 3582 := by
  rw [show (2763:Nat)=2662+(2763-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3858 : CycleSubmission.Artifact.artifact.instructionPC 2764 = 3583 := by
  rw [show (2764:Nat)=2662+(2764-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3859 : CycleSubmission.Artifact.artifact.instructionPC 2765 = 3584 := by
  rw [show (2765:Nat)=2662+(2765-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3860 : CycleSubmission.Artifact.artifact.instructionPC 2766 = 3587 := by
  rw [show (2766:Nat)=2662+(2766-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3861 : CycleSubmission.Artifact.artifact.instructionPC 2767 = 3588 := by
  rw [show (2767:Nat)=2662+(2767-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3862 : CycleSubmission.Artifact.artifact.instructionPC 2768 = 3589 := by
  rw [show (2768:Nat)=2662+(2768-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3863 : CycleSubmission.Artifact.artifact.instructionPC 2769 = 3590 := by
  rw [show (2769:Nat)=2662+(2769-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3864 : CycleSubmission.Artifact.artifact.instructionPC 2770 = 3591 := by
  rw [show (2770:Nat)=2662+(2770-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3865 : CycleSubmission.Artifact.artifact.instructionPC 2771 = 3594 := by
  rw [show (2771:Nat)=2662+(2771-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3866 : CycleSubmission.Artifact.artifact.instructionPC 2772 = 3595 := by
  rw [show (2772:Nat)=2662+(2772-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3867 : CycleSubmission.Artifact.artifact.instructionPC 2773 = 3596 := by
  rw [show (2773:Nat)=2662+(2773-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3868 : CycleSubmission.Artifact.artifact.instructionPC 2774 = 3597 := by
  rw [show (2774:Nat)=2662+(2774-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3869 : CycleSubmission.Artifact.artifact.instructionPC 2775 = 3598 := by
  rw [show (2775:Nat)=2662+(2775-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3871 : CycleSubmission.Artifact.artifact.instructionPC 2775 = 3598 := by
  rw [show (2775:Nat)=2662+(2775-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3872 : CycleSubmission.Artifact.artifact.instructionPC 2776 = 3599 := by
  rw [show (2776:Nat)=2662+(2776-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3873 : CycleSubmission.Artifact.artifact.instructionPC 2777 = 3600 := by
  rw [show (2777:Nat)=2662+(2777-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3874 : CycleSubmission.Artifact.artifact.instructionPC 2778 = 3602 := by
  rw [show (2778:Nat)=2662+(2778-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3875 : CycleSubmission.Artifact.artifact.instructionPC 2779 = 3603 := by
  rw [show (2779:Nat)=2662+(2779-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3876 : CycleSubmission.Artifact.artifact.instructionPC 2780 = 3604 := by
  rw [show (2780:Nat)=2662+(2780-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3877 : CycleSubmission.Artifact.artifact.instructionPC 2781 = 3605 := by
  rw [show (2781:Nat)=2662+(2781-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3878 : CycleSubmission.Artifact.artifact.instructionPC 2782 = 3608 := by
  rw [show (2782:Nat)=2662+(2782-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3879 : CycleSubmission.Artifact.artifact.instructionPC 2783 = 3609 := by
  rw [show (2783:Nat)=2662+(2783-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3880 : CycleSubmission.Artifact.artifact.instructionPC 2784 = 3610 := by
  rw [show (2784:Nat)=2662+(2784-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3881 : CycleSubmission.Artifact.artifact.instructionPC 2785 = 3611 := by
  rw [show (2785:Nat)=2662+(2785-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3882 : CycleSubmission.Artifact.artifact.instructionPC 2786 = 3612 := by
  rw [show (2786:Nat)=2662+(2786-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3883 : CycleSubmission.Artifact.artifact.instructionPC 2787 = 3615 := by
  rw [show (2787:Nat)=2662+(2787-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3884 : CycleSubmission.Artifact.artifact.instructionPC 2788 = 3616 := by
  rw [show (2788:Nat)=2662+(2788-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3885 : CycleSubmission.Artifact.artifact.instructionPC 2789 = 3617 := by
  rw [show (2789:Nat)=2662+(2789-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3886 : CycleSubmission.Artifact.artifact.instructionPC 2790 = 3618 := by
  rw [show (2790:Nat)=2662+(2790-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3887 : CycleSubmission.Artifact.artifact.instructionPC 2791 = 3619 := by
  rw [show (2791:Nat)=2662+(2791-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3888 : CycleSubmission.Artifact.artifact.instructionPC 2792 = 3620 := by
  rw [show (2792:Nat)=2662+(2792-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3889 : CycleSubmission.Artifact.artifact.instructionPC 2792 = 3620 := by
  rw [show (2792:Nat)=2662+(2792-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3620 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2792 = 3620 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2792 (by rfl)

@[simp] theorem fixedPC3890 : CycleSubmission.Artifact.artifact.instructionPC 2793 = 3621 := by
  rw [show (2793:Nat)=2662+(2793-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3891 : CycleSubmission.Artifact.artifact.instructionPC 2794 = 3622 := by
  rw [show (2794:Nat)=2662+(2794-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3892 : CycleSubmission.Artifact.artifact.instructionPC 2795 = 3624 := by
  rw [show (2795:Nat)=2662+(2795-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3893 : CycleSubmission.Artifact.artifact.instructionPC 2796 = 3625 := by
  rw [show (2796:Nat)=2662+(2796-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3894 : CycleSubmission.Artifact.artifact.instructionPC 2797 = 3626 := by
  rw [show (2797:Nat)=2662+(2797-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3895 : CycleSubmission.Artifact.artifact.instructionPC 2798 = 3627 := by
  rw [show (2798:Nat)=2662+(2798-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3896 : CycleSubmission.Artifact.artifact.instructionPC 2799 = 3630 := by
  rw [show (2799:Nat)=2662+(2799-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3897 : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3631 := by
  rw [show (2800:Nat)=2662+(2800-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3898 : CycleSubmission.Artifact.artifact.instructionPC 2801 = 3632 := by
  rw [show (2801:Nat)=2662+(2801-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3899 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3633 := by
  rw [show (2802:Nat)=2662+(2802-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3900 : CycleSubmission.Artifact.artifact.instructionPC 2803 = 3634 := by
  rw [show (2803:Nat)=2662+(2803-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3901 : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3637 := by
  rw [show (2804:Nat)=2662+(2804-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3902 : CycleSubmission.Artifact.artifact.instructionPC 2805 = 3638 := by
  rw [show (2805:Nat)=2662+(2805-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3903 : CycleSubmission.Artifact.artifact.instructionPC 2806 = 3639 := by
  rw [show (2806:Nat)=2662+(2806-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3904 : CycleSubmission.Artifact.artifact.instructionPC 2807 = 3640 := by
  rw [show (2807:Nat)=2662+(2807-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3905 : CycleSubmission.Artifact.artifact.instructionPC 2808 = 3641 := by
  rw [show (2808:Nat)=2662+(2808-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3906 : CycleSubmission.Artifact.artifact.instructionPC 2809 = 3642 := by
  rw [show (2809:Nat)=2662+(2809-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3907 : CycleSubmission.Artifact.artifact.instructionPC 2810 = 3643 := by
  rw [show (2810:Nat)=2662+(2810-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3908 : CycleSubmission.Artifact.artifact.instructionPC 2810 = 3643 := by
  rw [show (2810:Nat)=2662+(2810-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3909 : CycleSubmission.Artifact.artifact.instructionPC 2811 = 3645 := by
  rw [show (2811:Nat)=2662+(2811-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3910 : CycleSubmission.Artifact.artifact.instructionPC 2812 = 3646 := by
  rw [show (2812:Nat)=2662+(2812-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3911 : CycleSubmission.Artifact.artifact.instructionPC 2813 = 3647 := by
  rw [show (2813:Nat)=2662+(2813-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3912 : CycleSubmission.Artifact.artifact.instructionPC 2814 = 3648 := by
  rw [show (2814:Nat)=2662+(2814-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3913 : CycleSubmission.Artifact.artifact.instructionPC 2815 = 3651 := by
  rw [show (2815:Nat)=2662+(2815-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3914 : CycleSubmission.Artifact.artifact.instructionPC 2816 = 3652 := by
  rw [show (2816:Nat)=2662+(2816-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3915 : CycleSubmission.Artifact.artifact.instructionPC 2817 = 3653 := by
  rw [show (2817:Nat)=2662+(2817-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3916 : CycleSubmission.Artifact.artifact.instructionPC 2818 = 3654 := by
  rw [show (2818:Nat)=2662+(2818-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3917 : CycleSubmission.Artifact.artifact.instructionPC 2819 = 3655 := by
  rw [show (2819:Nat)=2662+(2819-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3918 : CycleSubmission.Artifact.artifact.instructionPC 2820 = 3658 := by
  rw [show (2820:Nat)=2662+(2820-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3919 : CycleSubmission.Artifact.artifact.instructionPC 2821 = 3659 := by
  rw [show (2821:Nat)=2662+(2821-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3920 : CycleSubmission.Artifact.artifact.instructionPC 2822 = 3660 := by
  rw [show (2822:Nat)=2662+(2822-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2823 = 3661 := by
  rw [show (2823:Nat)=2662+(2823-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2824 = 3662 := by
  rw [show (2824:Nat)=2662+(2824-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2825 = 3663 := by
  rw [show (2825:Nat)=2662+(2825-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2826 = 3664 := by
  rw [show (2826:Nat)=2662+(2826-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2827 = 3665 := by
  rw [show (2827:Nat)=2662+(2827-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2827 = 3665 := by
  rw [show (2827:Nat)=2662+(2827-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2828 = 3666 := by
  rw [show (2828:Nat)=2662+(2828-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2829 = 3667 := by
  rw [show (2829:Nat)=2662+(2829-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3929 : CycleSubmission.Artifact.artifact.instructionPC 2830 = 3668 := by
  rw [show (2830:Nat)=2662+(2830-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3930 : CycleSubmission.Artifact.artifact.instructionPC 2831 = 3671 := by
  rw [show (2831:Nat)=2662+(2831-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3931 : CycleSubmission.Artifact.artifact.instructionPC 2832 = 3672 := by
  rw [show (2832:Nat)=2662+(2832-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3932 : CycleSubmission.Artifact.artifact.instructionPC 2833 = 3673 := by
  rw [show (2833:Nat)=2662+(2833-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3933 : CycleSubmission.Artifact.artifact.instructionPC 2834 = 3674 := by
  rw [show (2834:Nat)=2662+(2834-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3934 : CycleSubmission.Artifact.artifact.instructionPC 2835 = 3675 := by
  rw [show (2835:Nat)=2662+(2835-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3935 : CycleSubmission.Artifact.artifact.instructionPC 2836 = 3678 := by
  rw [show (2836:Nat)=2662+(2836-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3936 : CycleSubmission.Artifact.artifact.instructionPC 2837 = 3679 := by
  rw [show (2837:Nat)=2662+(2837-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3937 : CycleSubmission.Artifact.artifact.instructionPC 2838 = 3680 := by
  rw [show (2838:Nat)=2662+(2838-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3938 : CycleSubmission.Artifact.artifact.instructionPC 2839 = 3681 := by
  rw [show (2839:Nat)=2662+(2839-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3939 : CycleSubmission.Artifact.artifact.instructionPC 2840 = 3682 := by
  rw [show (2840:Nat)=2662+(2840-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3940 : CycleSubmission.Artifact.artifact.instructionPC 2841 = 3683 := by
  rw [show (2841:Nat)=2662+(2841-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3941 : CycleSubmission.Artifact.artifact.instructionPC 2842 = 3684 := by
  rw [show (2842:Nat)=2662+(2842-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3942 : CycleSubmission.Artifact.artifact.instructionPC 2843 = 3687 := by
  rw [show (2843:Nat)=2662+(2843-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3943 : CycleSubmission.Artifact.artifact.instructionPC 2844 = 3688 := by
  rw [show (2844:Nat)=2662+(2844-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3944 : CycleSubmission.Artifact.artifact.instructionPC 2844 = 3688 := by
  rw [show (2844:Nat)=2662+(2844-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3945 : CycleSubmission.Artifact.artifact.instructionPC 2845 = 3689 := by
  rw [show (2845:Nat)=2662+(2845-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3946 : CycleSubmission.Artifact.artifact.instructionPC 2846 = 3692 := by
  rw [show (2846:Nat)=2662+(2846-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3947 : CycleSubmission.Artifact.artifact.instructionPC 2847 = 3693 := by
  rw [show (2847:Nat)=2662+(2847-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3948 : CycleSubmission.Artifact.artifact.instructionPC 2848 = 3696 := by
  rw [show (2848:Nat)=2662+(2848-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3949 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3714 := by
  rw [show (2862:Nat)=2662+(2862-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3950 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3714 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3715 := by
  rw [show (2863:Nat)=2662+(2863-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3952 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3716 := by
  rw [show (2864:Nat)=2662+(2864-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3953 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3717 := by
  rw [show (2865:Nat)=2662+(2865-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3954 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3718 := by
  rw [show (2866:Nat)=2662+(2866-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3955 : CycleSubmission.Artifact.artifact.instructionPC 2867 = 3721 := by
  rw [show (2867:Nat)=2662+(2867-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3956 : CycleSubmission.Artifact.artifact.instructionPC 2868 = 3724 := by
  rw [show (2868:Nat)=2662+(2868-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3957 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3725 := by
  rw [show (2869:Nat)=2662+(2869-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4190 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3477 := by
  rw [show (2687:Nat)=2662+(2687-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4193 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3478 := by
  rw [show (2688:Nat)=2662+(2688-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4194 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3481 := by
  rw [show (2689:Nat)=2662+(2689-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4547 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3726 := by
  rw [show (2870:Nat)=2662+(2870-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4548 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3727 := by
  rw [show (2871:Nat)=2662+(2871-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC3999 : CycleSubmission.Artifact.artifact.instructionPC 2673 = 3458 := by
  rw [show (2673:Nat)=2662+(2673-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3462 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3462 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2677 (by rfl)

@[simp] theorem fixedPC4000 : CycleSubmission.Artifact.artifact.instructionPC 2674 = 3459 := by
  rw [show (2674:Nat)=2662+(2674-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4001 : CycleSubmission.Artifact.artifact.instructionPC 2675 = 3460 := by
  rw [show (2675:Nat)=2662+(2675-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4002 : CycleSubmission.Artifact.artifact.instructionPC 2676 = 3461 := by
  rw [show (2676:Nat)=2662+(2676-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4003 : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3462 := by
  rw [show (2677:Nat)=2662+(2677-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4004 : CycleSubmission.Artifact.artifact.instructionPC 2678 = 3463 := by
  rw [show (2678:Nat)=2662+(2678-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4005 : CycleSubmission.Artifact.artifact.instructionPC 2679 = 3466 := by
  rw [show (2679:Nat)=2662+(2679-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4006 : CycleSubmission.Artifact.artifact.instructionPC 2680 = 3467 := by
  rw [show (2680:Nat)=2662+(2680-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4007 : CycleSubmission.Artifact.artifact.instructionPC 2681 = 3469 := by
  rw [show (2681:Nat)=2662+(2681-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4008 : CycleSubmission.Artifact.artifact.instructionPC 2682 = 3470 := by
  rw [show (2682:Nat)=2662+(2682-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4009 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3471 := by
  rw [show (2683:Nat)=2662+(2683-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4010 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3472 := by
  rw [show (2684:Nat)=2662+(2684-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4011 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3473 := by
  rw [show (2685:Nat)=2662+(2685-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4012 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3476 := by
  rw [show (2686:Nat)=2662+(2686-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2883 : CycleSubmission.Artifact.artifact.instructionPC 2642 = 3423 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : CycleSubmission.Artifact.artifact.instructionPC 2643 = 3424 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : CycleSubmission.Artifact.artifact.instructionPC 2644 = 3425 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : CycleSubmission.Artifact.artifact.instructionPC 2645 = 3426 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : CycleSubmission.Artifact.artifact.instructionPC 2646 = 3427 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : CycleSubmission.Artifact.artifact.instructionPC 2647 = 3428 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2890 : CycleSubmission.Artifact.artifact.instructionPC 2648 = 3429 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2891 : CycleSubmission.Artifact.artifact.instructionPC 2649 = 3432 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2892 : CycleSubmission.Artifact.artifact.instructionPC 2650 = 3433 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2893 : CycleSubmission.Artifact.artifact.instructionPC 2650 = 3433 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2894 : CycleSubmission.Artifact.artifact.instructionPC 2651 = 3436 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2895 : CycleSubmission.Artifact.artifact.instructionPC 2652 = 3437 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2896 : CycleSubmission.Artifact.artifact.instructionPC 2672 = 3457 := by
  rw [show (2672:Nat)=2662+(2672-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2930 : CycleSubmission.Artifact.artifact.instructionPC 2673 = 3458 := by
  rw [show (2673:Nat)=2662+(2673-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2931 : CycleSubmission.Artifact.artifact.instructionPC 2674 = 3459 := by
  rw [show (2674:Nat)=2662+(2674-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2932 : CycleSubmission.Artifact.artifact.instructionPC 2675 = 3460 := by
  rw [show (2675:Nat)=2662+(2675-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2933 : CycleSubmission.Artifact.artifact.instructionPC 2676 = 3461 := by
  rw [show (2676:Nat)=2662+(2676-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2934 : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3462 := by
  rw [show (2677:Nat)=2662+(2677-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2935 : CycleSubmission.Artifact.artifact.instructionPC 2678 = 3463 := by
  rw [show (2678:Nat)=2662+(2678-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2936 : CycleSubmission.Artifact.artifact.instructionPC 2679 = 3466 := by
  rw [show (2679:Nat)=2662+(2679-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2937 : CycleSubmission.Artifact.artifact.instructionPC 2680 = 3467 := by
  rw [show (2680:Nat)=2662+(2680-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2938 : CycleSubmission.Artifact.artifact.instructionPC 2681 = 3469 := by
  rw [show (2681:Nat)=2662+(2681-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2939 : CycleSubmission.Artifact.artifact.instructionPC 2682 = 3470 := by
  rw [show (2682:Nat)=2662+(2682-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2940 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3471 := by
  rw [show (2683:Nat)=2662+(2683-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2941 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3472 := by
  rw [show (2684:Nat)=2662+(2684-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2942 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3473 := by
  rw [show (2685:Nat)=2662+(2685-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2943 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3476 := by
  rw [show (2686:Nat)=2662+(2686-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3702 := by
  rw [show (2854:Nat)=2662+(2854-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3703 := by
  rw [show (2855:Nat)=2662+(2855-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3704 := by
  rw [show (2856:Nat)=2662+(2856-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3705 := by
  rw [show (2857:Nat)=2662+(2857-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2858 = 3706 := by
  rw [show (2858:Nat)=2662+(2858-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2859 = 3707 := by
  rw [show (2859:Nat)=2662+(2859-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3710 := by
  rw [show (2860:Nat)=2662+(2860-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3713 := by
  rw [show (2861:Nat)=2662+(2861-2662) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

end CycleSubmission.Global.Fast
