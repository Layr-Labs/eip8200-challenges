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
  [opAt 2704 .JUMPDEST,
   pushAt 2705 2 2688,
   opAt 2706 .MLOAD,
   pushAt 2707 1 128,
   opAt 2708 .EQ,
   pushAt 2709 2 3468,
   opAt 2710 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2704 .JUMPDEST,
   pushAt 2705 2 2688,
   opAt 2706 .MLOAD,
   pushAt 2707 1 128,
   opAt 2708 .EQ,
   pushAt 2709 2 3468,
   opAt 2710 .JUMPI,
   opAt 2677 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2711 .JUMPDEST,
   pushAt 2712 2 2336,
   opAt 2713 .MLOAD,
   pushAt 2714 1 224,
   opAt 2715 .MLOAD,
   opAt 2716 (.Dup ⟨0, by decide⟩),
   opAt 2717 (.Dup ⟨2, by decide⟩),
   opAt 2718 .SUB,
   pushAt 2719 2 2016,
   opAt 2720 .MSTORE,
   opAt 2721 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2722 (.Dup ⟨0, by decide⟩),
   pushAt 2723 1 192,
   opAt 2724 .MLOAD,
   opAt 2725 .ADD,
   opAt 2726 (.Dup ⟨0, by decide⟩),
   pushAt 2727 2 2304,
   opAt 2728 .MLOAD,
   opAt 2729 (.Dup ⟨1, by decide⟩),
   opAt 2730 (.Dup ⟨1, by decide⟩),
   opAt 2731 .SUB,
   pushAt 2732 2 1984,
   opAt 2733 .MSTORE,
   opAt 2734 .LT,
   opAt 2735 (.Swap ⟨1, by decide⟩),
   opAt 2736 .GT,
   opAt 2737 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2738 (.Dup ⟨0, by decide⟩),
   pushAt 2739 1 160,
   opAt 2740 .MLOAD,
   opAt 2741 .ADD,
   opAt 2742 (.Dup ⟨0, by decide⟩),
   pushAt 2743 2 2272,
   opAt 2744 .MLOAD,
   opAt 2745 (.Dup ⟨1, by decide⟩),
   opAt 2746 (.Dup ⟨1, by decide⟩),
   opAt 2747 .SUB,
   pushAt 2748 2 1952,
   opAt 2749 .MSTORE,
   opAt 2750 .LT,
   opAt 2751 (.Swap ⟨1, by decide⟩),
   opAt 2752 .GT,
   opAt 2753 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2754 (.Dup ⟨0, by decide⟩),
   pushAt 2755 1 128,
   opAt 2756 .MLOAD,
   opAt 2757 .ADD,
   opAt 2758 (.Dup ⟨0, by decide⟩),
   pushAt 2759 2 2240,
   opAt 2760 .MLOAD,
   opAt 2761 (.Dup ⟨1, by decide⟩),
   opAt 2762 (.Dup ⟨1, by decide⟩),
   opAt 2763 .SUB,
   pushAt 2764 2 1920,
   opAt 2765 .MSTORE,
   opAt 2766 .LT,
   opAt 2767 (.Swap ⟨1, by decide⟩),
   opAt 2768 .GT,
   opAt 2769 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2770 (.Dup ⟨0, by decide⟩),
   pushAt 2771 1 96,
   opAt 2772 .MLOAD,
   opAt 2773 .ADD,
   opAt 2774 (.Dup ⟨0, by decide⟩),
   pushAt 2775 2 2208,
   opAt 2776 .MLOAD,
   opAt 2777 (.Dup ⟨1, by decide⟩),
   opAt 2778 (.Dup ⟨1, by decide⟩),
   opAt 2779 .SUB,
   pushAt 2780 2 1888,
   opAt 2781 .MSTORE,
   opAt 2782 .LT,
   opAt 2783 (.Swap ⟨1, by decide⟩),
   opAt 2784 .GT,
   opAt 2785 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2786 .JUMPDEST,
   opAt 2787 (.Dup ⟨0, by decide⟩),
   pushAt 2788 1 64,
   opAt 2789 .MLOAD,
   opAt 2790 .ADD,
   opAt 2791 (.Dup ⟨0, by decide⟩),
   pushAt 2792 2 2176,
   opAt 2793 .MLOAD,
   opAt 2794 (.Dup ⟨1, by decide⟩),
   opAt 2795 (.Dup ⟨1, by decide⟩),
   opAt 2796 .SUB,
   pushAt 2797 2 1856,
   opAt 2798 .MSTORE,
   opAt 2799 .LT,
   opAt 2800 (.Swap ⟨1, by decide⟩),
   opAt 2801 .GT,
   opAt 2802 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2803 (.Dup ⟨0, by decide⟩),
   pushAt 2804 1 32,
   opAt 2805 .MLOAD,
   opAt 2806 .ADD,
   opAt 2807 (.Dup ⟨0, by decide⟩),
   pushAt 2808 2 2144,
   opAt 2809 .MLOAD,
   opAt 2810 (.Dup ⟨1, by decide⟩),
   opAt 2811 (.Dup ⟨1, by decide⟩),
   opAt 2812 .SUB,
   pushAt 2813 2 1824,
   opAt 2814 .MSTORE,
   opAt 2815 .LT,
   opAt 2816 (.Swap ⟨1, by decide⟩),
   opAt 2817 .GT,
   opAt 2818 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2819 (.Dup ⟨0, by decide⟩),
   pushAt 2820 0 0,
   opAt 2821 .MLOAD,
   opAt 2822 .ADD,
   opAt 2823 (.Dup ⟨0, by decide⟩),
   pushAt 2824 2 2112,
   opAt 2825 .MLOAD,
   opAt 2826 (.Dup ⟨1, by decide⟩),
   opAt 2827 (.Dup ⟨1, by decide⟩),
   opAt 2828 .SUB,
   pushAt 2829 2 1792,
   opAt 2830 .MSTORE,
   opAt 2831 .LT,
   opAt 2832 (.Swap ⟨1, by decide⟩),
   opAt 2833 .GT,
   opAt 2834 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2835 .ISZERO,
   pushAt 2836 2 2080,
   opAt 2837 .MLOAD,
   opAt 2838 .OR,
   pushAt 2839 2 3717,
   opAt 2840 .JUMPI,
   opAt 2859 .JUMPDEST,
   pushAt 2860 2 1792,
   pushAt 2861 2 2688,
   opAt 2862 .MLOAD,
   opAt 2863 (.Swap ⟨1, by decide⟩),
   opAt 2864 .MCOPY,
   opAt 2865 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2835 .ISZERO,
   pushAt 2836 2 2080,
   opAt 2837 .MLOAD,
   opAt 2838 .OR,
   pushAt 2839 2 3717,
   opAt 2840 .JUMPI,
   pushAt 2841 2 3706,
   opAt 2842 .JUMP,
   opAt 2852 .JUMPDEST,
   pushAt 2853 2 2112,
   pushAt 2854 2 2688,
   opAt 2855 .MLOAD,
   opAt 2856 (.Swap ⟨1, by decide⟩),
   opAt 2857 .MCOPY,
   opAt 2858 .JUMP]

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
  [opAt 2786 .JUMPDEST,
   opAt 2787 (.Dup ⟨0, by decide⟩),
   pushAt 2788 1 64,
   opAt 2789 .MLOAD,
   opAt 2790 .ADD,
   opAt 2791 (.Dup ⟨0, by decide⟩),
   pushAt 2792 2 2176,
   opAt 2793 .MLOAD,
   opAt 2794 (.Dup ⟨1, by decide⟩),
   opAt 2795 (.Dup ⟨1, by decide⟩),
   opAt 2796 .SUB,
   pushAt 2797 2 1856,
   opAt 2798 .MSTORE,
   opAt 2799 .LT,
   opAt 2800 (.Swap ⟨1, by decide⟩),
   opAt 2801 .GT,
   opAt 2802 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2803 (.Dup ⟨0, by decide⟩),
   pushAt 2804 1 32,
   opAt 2805 .MLOAD,
   opAt 2806 .ADD,
   opAt 2807 (.Dup ⟨0, by decide⟩),
   pushAt 2808 2 2144,
   opAt 2809 .MLOAD,
   opAt 2810 (.Dup ⟨1, by decide⟩),
   opAt 2811 (.Dup ⟨1, by decide⟩),
   opAt 2812 .SUB,
   pushAt 2813 2 1824,
   opAt 2814 .MSTORE,
   opAt 2815 .LT,
   opAt 2816 (.Swap ⟨1, by decide⟩),
   opAt 2817 .GT,
   opAt 2818 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2819 (.Dup ⟨0, by decide⟩),
   pushAt 2820 0 0,
   opAt 2821 .MLOAD,
   opAt 2822 .ADD,
   opAt 2823 (.Dup ⟨0, by decide⟩),
   pushAt 2824 2 2112,
   opAt 2825 .MLOAD,
   opAt 2826 (.Dup ⟨1, by decide⟩),
   opAt 2827 (.Dup ⟨1, by decide⟩),
   opAt 2828 .SUB,
   pushAt 2829 2 1792,
   opAt 2830 .MSTORE,
   opAt 2831 .LT,
   opAt 2832 (.Swap ⟨1, by decide⟩),
   opAt 2833 .GT,
   opAt 2834 .OR]

private theorem cycleAnchor : CycleSubmission.Artifact.artifact.instructionPC 2671 = 3458 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem fixedPC3777 : CycleSubmission.Artifact.artifact.instructionPC 2700 = 3500 := by
  rw [show (2700:Nat)=2671+(2700-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3508 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2704 = 3508 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2704 (by rfl)

@[simp] theorem fixedPC3778 : CycleSubmission.Artifact.artifact.instructionPC 2841 = 3693 := by
  rw [show (2841:Nat)=2671+(2841-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3779 : CycleSubmission.Artifact.artifact.instructionPC 2842 = 3696 := by
  rw [show (2842:Nat)=2671+(2842-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3792 : CycleSubmission.Artifact.artifact.instructionPC 2852 = 3706 := by
  rw [show (2852:Nat)=2671+(2852-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3793 : CycleSubmission.Artifact.artifact.instructionPC 2853 = 3707 := by
  rw [show (2853:Nat)=2671+(2853-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3794 : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3710 := by
  rw [show (2854:Nat)=2671+(2854-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3795 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3713 := by
  rw [show (2855:Nat)=2671+(2855-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3796 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3714 := by
  rw [show (2856:Nat)=2671+(2856-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3797 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3715 := by
  rw [show (2857:Nat)=2671+(2857-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3798 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3715 := fixedPC3797

@[simp] theorem fixedPC3799 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3715 := fixedPC3797

@[simp] theorem fixedPC3800 : CycleSubmission.Artifact.artifact.instructionPC 2858 = 3716 := by
  rw [show (2858:Nat)=2671+(2858-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3801 : CycleSubmission.Artifact.artifact.instructionPC 2859 = 3717 := by
  rw [show (2859:Nat)=2671+(2859-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3802 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3718 := by
  rw [show (2860:Nat)=2671+(2860-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3803 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3721 := by
  rw [show (2861:Nat)=2671+(2861-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3804 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3724 := by
  rw [show (2862:Nat)=2671+(2862-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : CycleSubmission.Artifact.artifact.instructionPC 2701 = 3501 := by
  rw [show (2701:Nat)=2671+(2701-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3115 : CycleSubmission.Artifact.artifact.instructionPC 2702 = 3504 := by
  rw [show (2702:Nat)=2671+(2702-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3116 : CycleSubmission.Artifact.artifact.instructionPC 2703 = 3505 := by
  rw [show (2703:Nat)=2671+(2703-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3117 : CycleSubmission.Artifact.artifact.instructionPC 2704 = 3508 := by
  rw [show (2704:Nat)=2671+(2704-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3118 : CycleSubmission.Artifact.artifact.instructionPC 2705 = 3509 := by
  rw [show (2705:Nat)=2671+(2705-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3119 : CycleSubmission.Artifact.artifact.instructionPC 2706 = 3512 := by
  rw [show (2706:Nat)=2671+(2706-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3468 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3468 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2677 (by rfl)

@[simp] theorem fixedPC3805 : CycleSubmission.Artifact.artifact.instructionPC 2707 = 3513 := by
  rw [show (2707:Nat)=2671+(2707-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3806 : CycleSubmission.Artifact.artifact.instructionPC 2708 = 3515 := by
  rw [show (2708:Nat)=2671+(2708-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3807 : CycleSubmission.Artifact.artifact.instructionPC 2709 = 3516 := by
  rw [show (2709:Nat)=2671+(2709-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3808 : CycleSubmission.Artifact.artifact.instructionPC 2710 = 3519 := by
  rw [show (2710:Nat)=2671+(2710-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPCs8 : CycleSubmission.Artifact.artifact.instructionPC 2711 = 3520 := by
  rw [show (2711:Nat)=2671+(2711-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3809 : CycleSubmission.Artifact.artifact.instructionPC 2712 = 3521 := by
  rw [show (2712:Nat)=2671+(2712-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3810 : CycleSubmission.Artifact.artifact.instructionPC 2713 = 3524 := by
  rw [show (2713:Nat)=2671+(2713-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3811 : CycleSubmission.Artifact.artifact.instructionPC 2714 = 3525 := by
  rw [show (2714:Nat)=2671+(2714-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3812 : CycleSubmission.Artifact.artifact.instructionPC 2715 = 3527 := by
  rw [show (2715:Nat)=2671+(2715-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3813 : CycleSubmission.Artifact.artifact.instructionPC 2716 = 3528 := by
  rw [show (2716:Nat)=2671+(2716-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3814 : CycleSubmission.Artifact.artifact.instructionPC 2717 = 3529 := by
  rw [show (2717:Nat)=2671+(2717-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3815 : CycleSubmission.Artifact.artifact.instructionPC 2718 = 3530 := by
  rw [show (2718:Nat)=2671+(2718-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3816 : CycleSubmission.Artifact.artifact.instructionPC 2718 = 3530 := by
  rw [show (2718:Nat)=2671+(2718-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3817 : CycleSubmission.Artifact.artifact.instructionPC 2719 = 3531 := by
  rw [show (2719:Nat)=2671+(2719-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3818 : CycleSubmission.Artifact.artifact.instructionPC 2720 = 3534 := by
  rw [show (2720:Nat)=2671+(2720-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3819 : CycleSubmission.Artifact.artifact.instructionPC 2721 = 3535 := by
  rw [show (2721:Nat)=2671+(2721-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3820 : CycleSubmission.Artifact.artifact.instructionPC 2722 = 3536 := by
  rw [show (2722:Nat)=2671+(2722-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3821 : CycleSubmission.Artifact.artifact.instructionPC 2723 = 3537 := by
  rw [show (2723:Nat)=2671+(2723-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3822 : CycleSubmission.Artifact.artifact.instructionPC 2724 = 3539 := by
  rw [show (2724:Nat)=2671+(2724-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3823 : CycleSubmission.Artifact.artifact.instructionPC 2725 = 3540 := by
  rw [show (2725:Nat)=2671+(2725-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3824 : CycleSubmission.Artifact.artifact.instructionPC 2726 = 3541 := by
  rw [show (2726:Nat)=2671+(2726-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3825 : CycleSubmission.Artifact.artifact.instructionPC 2727 = 3542 := by
  rw [show (2727:Nat)=2671+(2727-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3826 : CycleSubmission.Artifact.artifact.instructionPC 2728 = 3545 := by
  rw [show (2728:Nat)=2671+(2728-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3827 : CycleSubmission.Artifact.artifact.instructionPC 2729 = 3546 := by
  rw [show (2729:Nat)=2671+(2729-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3828 : CycleSubmission.Artifact.artifact.instructionPC 2730 = 3547 := by
  rw [show (2730:Nat)=2671+(2730-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3829 : CycleSubmission.Artifact.artifact.instructionPC 2731 = 3548 := by
  rw [show (2731:Nat)=2671+(2731-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3830 : CycleSubmission.Artifact.artifact.instructionPC 2732 = 3549 := by
  rw [show (2732:Nat)=2671+(2732-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3831 : CycleSubmission.Artifact.artifact.instructionPC 2733 = 3552 := by
  rw [show (2733:Nat)=2671+(2733-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3832 : CycleSubmission.Artifact.artifact.instructionPC 2734 = 3553 := by
  rw [show (2734:Nat)=2671+(2734-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3833 : CycleSubmission.Artifact.artifact.instructionPC 2735 = 3554 := by
  rw [show (2735:Nat)=2671+(2735-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3834 : CycleSubmission.Artifact.artifact.instructionPC 2735 = 3554 := by
  rw [show (2735:Nat)=2671+(2735-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3835 : CycleSubmission.Artifact.artifact.instructionPC 2736 = 3555 := by
  rw [show (2736:Nat)=2671+(2736-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3836 : CycleSubmission.Artifact.artifact.instructionPC 2737 = 3556 := by
  rw [show (2737:Nat)=2671+(2737-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3837 : CycleSubmission.Artifact.artifact.instructionPC 2738 = 3557 := by
  rw [show (2738:Nat)=2671+(2738-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3838 : CycleSubmission.Artifact.artifact.instructionPC 2739 = 3558 := by
  rw [show (2739:Nat)=2671+(2739-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3839 : CycleSubmission.Artifact.artifact.instructionPC 2740 = 3560 := by
  rw [show (2740:Nat)=2671+(2740-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3840 : CycleSubmission.Artifact.artifact.instructionPC 2741 = 3561 := by
  rw [show (2741:Nat)=2671+(2741-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3841 : CycleSubmission.Artifact.artifact.instructionPC 2742 = 3562 := by
  rw [show (2742:Nat)=2671+(2742-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3842 : CycleSubmission.Artifact.artifact.instructionPC 2743 = 3563 := by
  rw [show (2743:Nat)=2671+(2743-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3843 : CycleSubmission.Artifact.artifact.instructionPC 2744 = 3566 := by
  rw [show (2744:Nat)=2671+(2744-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3844 : CycleSubmission.Artifact.artifact.instructionPC 2745 = 3567 := by
  rw [show (2745:Nat)=2671+(2745-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3845 : CycleSubmission.Artifact.artifact.instructionPC 2746 = 3568 := by
  rw [show (2746:Nat)=2671+(2746-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3846 : CycleSubmission.Artifact.artifact.instructionPC 2747 = 3569 := by
  rw [show (2747:Nat)=2671+(2747-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3847 : CycleSubmission.Artifact.artifact.instructionPC 2748 = 3570 := by
  rw [show (2748:Nat)=2671+(2748-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3848 : CycleSubmission.Artifact.artifact.instructionPC 2749 = 3573 := by
  rw [show (2749:Nat)=2671+(2749-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3849 : CycleSubmission.Artifact.artifact.instructionPC 2750 = 3574 := by
  rw [show (2750:Nat)=2671+(2750-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3850 : CycleSubmission.Artifact.artifact.instructionPC 2751 = 3575 := by
  rw [show (2751:Nat)=2671+(2751-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3851 : CycleSubmission.Artifact.artifact.instructionPC 2752 = 3576 := by
  rw [show (2752:Nat)=2671+(2752-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3852 : CycleSubmission.Artifact.artifact.instructionPC 2752 = 3576 := by
  rw [show (2752:Nat)=2671+(2752-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3853 : CycleSubmission.Artifact.artifact.instructionPC 2753 = 3577 := by
  rw [show (2753:Nat)=2671+(2753-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3854 : CycleSubmission.Artifact.artifact.instructionPC 2754 = 3578 := by
  rw [show (2754:Nat)=2671+(2754-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3855 : CycleSubmission.Artifact.artifact.instructionPC 2755 = 3579 := by
  rw [show (2755:Nat)=2671+(2755-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3856 : CycleSubmission.Artifact.artifact.instructionPC 2756 = 3581 := by
  rw [show (2756:Nat)=2671+(2756-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3857 : CycleSubmission.Artifact.artifact.instructionPC 2757 = 3582 := by
  rw [show (2757:Nat)=2671+(2757-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3858 : CycleSubmission.Artifact.artifact.instructionPC 2758 = 3583 := by
  rw [show (2758:Nat)=2671+(2758-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3859 : CycleSubmission.Artifact.artifact.instructionPC 2759 = 3584 := by
  rw [show (2759:Nat)=2671+(2759-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3860 : CycleSubmission.Artifact.artifact.instructionPC 2760 = 3587 := by
  rw [show (2760:Nat)=2671+(2760-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3861 : CycleSubmission.Artifact.artifact.instructionPC 2761 = 3588 := by
  rw [show (2761:Nat)=2671+(2761-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3862 : CycleSubmission.Artifact.artifact.instructionPC 2762 = 3589 := by
  rw [show (2762:Nat)=2671+(2762-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3863 : CycleSubmission.Artifact.artifact.instructionPC 2763 = 3590 := by
  rw [show (2763:Nat)=2671+(2763-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3864 : CycleSubmission.Artifact.artifact.instructionPC 2764 = 3591 := by
  rw [show (2764:Nat)=2671+(2764-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3865 : CycleSubmission.Artifact.artifact.instructionPC 2765 = 3594 := by
  rw [show (2765:Nat)=2671+(2765-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3866 : CycleSubmission.Artifact.artifact.instructionPC 2766 = 3595 := by
  rw [show (2766:Nat)=2671+(2766-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3867 : CycleSubmission.Artifact.artifact.instructionPC 2767 = 3596 := by
  rw [show (2767:Nat)=2671+(2767-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3868 : CycleSubmission.Artifact.artifact.instructionPC 2768 = 3597 := by
  rw [show (2768:Nat)=2671+(2768-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3869 : CycleSubmission.Artifact.artifact.instructionPC 2769 = 3598 := by
  rw [show (2769:Nat)=2671+(2769-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3871 : CycleSubmission.Artifact.artifact.instructionPC 2769 = 3598 := by
  rw [show (2769:Nat)=2671+(2769-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3872 : CycleSubmission.Artifact.artifact.instructionPC 2770 = 3599 := by
  rw [show (2770:Nat)=2671+(2770-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3873 : CycleSubmission.Artifact.artifact.instructionPC 2771 = 3600 := by
  rw [show (2771:Nat)=2671+(2771-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3874 : CycleSubmission.Artifact.artifact.instructionPC 2772 = 3602 := by
  rw [show (2772:Nat)=2671+(2772-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3875 : CycleSubmission.Artifact.artifact.instructionPC 2773 = 3603 := by
  rw [show (2773:Nat)=2671+(2773-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3876 : CycleSubmission.Artifact.artifact.instructionPC 2774 = 3604 := by
  rw [show (2774:Nat)=2671+(2774-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3877 : CycleSubmission.Artifact.artifact.instructionPC 2775 = 3605 := by
  rw [show (2775:Nat)=2671+(2775-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3878 : CycleSubmission.Artifact.artifact.instructionPC 2776 = 3608 := by
  rw [show (2776:Nat)=2671+(2776-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3879 : CycleSubmission.Artifact.artifact.instructionPC 2777 = 3609 := by
  rw [show (2777:Nat)=2671+(2777-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3880 : CycleSubmission.Artifact.artifact.instructionPC 2778 = 3610 := by
  rw [show (2778:Nat)=2671+(2778-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3881 : CycleSubmission.Artifact.artifact.instructionPC 2779 = 3611 := by
  rw [show (2779:Nat)=2671+(2779-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3882 : CycleSubmission.Artifact.artifact.instructionPC 2780 = 3612 := by
  rw [show (2780:Nat)=2671+(2780-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3883 : CycleSubmission.Artifact.artifact.instructionPC 2781 = 3615 := by
  rw [show (2781:Nat)=2671+(2781-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3884 : CycleSubmission.Artifact.artifact.instructionPC 2782 = 3616 := by
  rw [show (2782:Nat)=2671+(2782-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3885 : CycleSubmission.Artifact.artifact.instructionPC 2783 = 3617 := by
  rw [show (2783:Nat)=2671+(2783-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3886 : CycleSubmission.Artifact.artifact.instructionPC 2784 = 3618 := by
  rw [show (2784:Nat)=2671+(2784-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3887 : CycleSubmission.Artifact.artifact.instructionPC 2785 = 3619 := by
  rw [show (2785:Nat)=2671+(2785-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3888 : CycleSubmission.Artifact.artifact.instructionPC 2786 = 3620 := by
  rw [show (2786:Nat)=2671+(2786-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3889 : CycleSubmission.Artifact.artifact.instructionPC 2786 = 3620 := by
  rw [show (2786:Nat)=2671+(2786-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3620 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2786 = 3620 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2786 (by rfl)

@[simp] theorem fixedPC3890 : CycleSubmission.Artifact.artifact.instructionPC 2787 = 3621 := by
  rw [show (2787:Nat)=2671+(2787-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3891 : CycleSubmission.Artifact.artifact.instructionPC 2788 = 3622 := by
  rw [show (2788:Nat)=2671+(2788-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3892 : CycleSubmission.Artifact.artifact.instructionPC 2789 = 3624 := by
  rw [show (2789:Nat)=2671+(2789-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3893 : CycleSubmission.Artifact.artifact.instructionPC 2790 = 3625 := by
  rw [show (2790:Nat)=2671+(2790-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3894 : CycleSubmission.Artifact.artifact.instructionPC 2791 = 3626 := by
  rw [show (2791:Nat)=2671+(2791-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3895 : CycleSubmission.Artifact.artifact.instructionPC 2792 = 3627 := by
  rw [show (2792:Nat)=2671+(2792-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3896 : CycleSubmission.Artifact.artifact.instructionPC 2793 = 3630 := by
  rw [show (2793:Nat)=2671+(2793-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3897 : CycleSubmission.Artifact.artifact.instructionPC 2794 = 3631 := by
  rw [show (2794:Nat)=2671+(2794-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3898 : CycleSubmission.Artifact.artifact.instructionPC 2795 = 3632 := by
  rw [show (2795:Nat)=2671+(2795-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3899 : CycleSubmission.Artifact.artifact.instructionPC 2796 = 3633 := by
  rw [show (2796:Nat)=2671+(2796-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3900 : CycleSubmission.Artifact.artifact.instructionPC 2797 = 3634 := by
  rw [show (2797:Nat)=2671+(2797-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3901 : CycleSubmission.Artifact.artifact.instructionPC 2798 = 3637 := by
  rw [show (2798:Nat)=2671+(2798-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3902 : CycleSubmission.Artifact.artifact.instructionPC 2799 = 3638 := by
  rw [show (2799:Nat)=2671+(2799-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3903 : CycleSubmission.Artifact.artifact.instructionPC 2800 = 3639 := by
  rw [show (2800:Nat)=2671+(2800-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3904 : CycleSubmission.Artifact.artifact.instructionPC 2801 = 3640 := by
  rw [show (2801:Nat)=2671+(2801-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3905 : CycleSubmission.Artifact.artifact.instructionPC 2802 = 3641 := by
  rw [show (2802:Nat)=2671+(2802-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3906 : CycleSubmission.Artifact.artifact.instructionPC 2803 = 3642 := by
  rw [show (2803:Nat)=2671+(2803-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3907 : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3643 := by
  rw [show (2804:Nat)=2671+(2804-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3908 : CycleSubmission.Artifact.artifact.instructionPC 2804 = 3643 := by
  rw [show (2804:Nat)=2671+(2804-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3909 : CycleSubmission.Artifact.artifact.instructionPC 2805 = 3645 := by
  rw [show (2805:Nat)=2671+(2805-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3910 : CycleSubmission.Artifact.artifact.instructionPC 2806 = 3646 := by
  rw [show (2806:Nat)=2671+(2806-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3911 : CycleSubmission.Artifact.artifact.instructionPC 2807 = 3647 := by
  rw [show (2807:Nat)=2671+(2807-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3912 : CycleSubmission.Artifact.artifact.instructionPC 2808 = 3648 := by
  rw [show (2808:Nat)=2671+(2808-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3913 : CycleSubmission.Artifact.artifact.instructionPC 2809 = 3651 := by
  rw [show (2809:Nat)=2671+(2809-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3914 : CycleSubmission.Artifact.artifact.instructionPC 2810 = 3652 := by
  rw [show (2810:Nat)=2671+(2810-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3915 : CycleSubmission.Artifact.artifact.instructionPC 2811 = 3653 := by
  rw [show (2811:Nat)=2671+(2811-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3916 : CycleSubmission.Artifact.artifact.instructionPC 2812 = 3654 := by
  rw [show (2812:Nat)=2671+(2812-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3917 : CycleSubmission.Artifact.artifact.instructionPC 2813 = 3655 := by
  rw [show (2813:Nat)=2671+(2813-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3918 : CycleSubmission.Artifact.artifact.instructionPC 2814 = 3658 := by
  rw [show (2814:Nat)=2671+(2814-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3919 : CycleSubmission.Artifact.artifact.instructionPC 2815 = 3659 := by
  rw [show (2815:Nat)=2671+(2815-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3920 : CycleSubmission.Artifact.artifact.instructionPC 2816 = 3660 := by
  rw [show (2816:Nat)=2671+(2816-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3921 : CycleSubmission.Artifact.artifact.instructionPC 2817 = 3661 := by
  rw [show (2817:Nat)=2671+(2817-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3922 : CycleSubmission.Artifact.artifact.instructionPC 2818 = 3662 := by
  rw [show (2818:Nat)=2671+(2818-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3923 : CycleSubmission.Artifact.artifact.instructionPC 2819 = 3663 := by
  rw [show (2819:Nat)=2671+(2819-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3924 : CycleSubmission.Artifact.artifact.instructionPC 2820 = 3664 := by
  rw [show (2820:Nat)=2671+(2820-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2821 = 3665 := by
  rw [show (2821:Nat)=2671+(2821-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2821 = 3665 := by
  rw [show (2821:Nat)=2671+(2821-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2822 = 3666 := by
  rw [show (2822:Nat)=2671+(2822-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2823 = 3667 := by
  rw [show (2823:Nat)=2671+(2823-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3929 : CycleSubmission.Artifact.artifact.instructionPC 2824 = 3668 := by
  rw [show (2824:Nat)=2671+(2824-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3930 : CycleSubmission.Artifact.artifact.instructionPC 2825 = 3671 := by
  rw [show (2825:Nat)=2671+(2825-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3931 : CycleSubmission.Artifact.artifact.instructionPC 2826 = 3672 := by
  rw [show (2826:Nat)=2671+(2826-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3932 : CycleSubmission.Artifact.artifact.instructionPC 2827 = 3673 := by
  rw [show (2827:Nat)=2671+(2827-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3933 : CycleSubmission.Artifact.artifact.instructionPC 2828 = 3674 := by
  rw [show (2828:Nat)=2671+(2828-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3934 : CycleSubmission.Artifact.artifact.instructionPC 2829 = 3675 := by
  rw [show (2829:Nat)=2671+(2829-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3935 : CycleSubmission.Artifact.artifact.instructionPC 2830 = 3678 := by
  rw [show (2830:Nat)=2671+(2830-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3936 : CycleSubmission.Artifact.artifact.instructionPC 2831 = 3679 := by
  rw [show (2831:Nat)=2671+(2831-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3937 : CycleSubmission.Artifact.artifact.instructionPC 2832 = 3680 := by
  rw [show (2832:Nat)=2671+(2832-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3938 : CycleSubmission.Artifact.artifact.instructionPC 2833 = 3681 := by
  rw [show (2833:Nat)=2671+(2833-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3939 : CycleSubmission.Artifact.artifact.instructionPC 2834 = 3682 := by
  rw [show (2834:Nat)=2671+(2834-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3940 : CycleSubmission.Artifact.artifact.instructionPC 2835 = 3683 := by
  rw [show (2835:Nat)=2671+(2835-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3941 : CycleSubmission.Artifact.artifact.instructionPC 2836 = 3684 := by
  rw [show (2836:Nat)=2671+(2836-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3942 : CycleSubmission.Artifact.artifact.instructionPC 2837 = 3687 := by
  rw [show (2837:Nat)=2671+(2837-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3943 : CycleSubmission.Artifact.artifact.instructionPC 2838 = 3688 := by
  rw [show (2838:Nat)=2671+(2838-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3944 : CycleSubmission.Artifact.artifact.instructionPC 2838 = 3688 := by
  rw [show (2838:Nat)=2671+(2838-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3945 : CycleSubmission.Artifact.artifact.instructionPC 2839 = 3689 := by
  rw [show (2839:Nat)=2671+(2839-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3946 : CycleSubmission.Artifact.artifact.instructionPC 2840 = 3692 := by
  rw [show (2840:Nat)=2671+(2840-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3947 : CycleSubmission.Artifact.artifact.instructionPC 2841 = 3693 := by
  rw [show (2841:Nat)=2671+(2841-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3948 : CycleSubmission.Artifact.artifact.instructionPC 2842 = 3696 := by
  rw [show (2842:Nat)=2671+(2842-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3949 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3714 := by
  rw [show (2856:Nat)=2671+(2856-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3950 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3714 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3715 := by
  rw [show (2857:Nat)=2671+(2857-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3952 : CycleSubmission.Artifact.artifact.instructionPC 2858 = 3716 := by
  rw [show (2858:Nat)=2671+(2858-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3953 : CycleSubmission.Artifact.artifact.instructionPC 2859 = 3717 := by
  rw [show (2859:Nat)=2671+(2859-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3954 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3718 := by
  rw [show (2860:Nat)=2671+(2860-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3955 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3721 := by
  rw [show (2861:Nat)=2671+(2861-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3956 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3724 := by
  rw [show (2862:Nat)=2671+(2862-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC3957 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3725 := by
  rw [show (2863:Nat)=2671+(2863-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4190 : CycleSubmission.Artifact.artifact.instructionPC 2687 = 3483 := by
  rw [show (2687:Nat)=2671+(2687-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4193 : CycleSubmission.Artifact.artifact.instructionPC 2688 = 3484 := by
  rw [show (2688:Nat)=2671+(2688-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4194 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3487 := by
  rw [show (2689:Nat)=2671+(2689-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4547 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3726 := by
  rw [show (2864:Nat)=2671+(2864-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedPC4548 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3727 := by
  rw [show (2865:Nat)=2671+(2865-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl
@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3468 = true := by
  have h : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3468 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 2677 (by rfl)

@[simp] theorem fixedPC4003 : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3468 := by
  rw [show (2677:Nat)=2671+(2677-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4004 : CycleSubmission.Artifact.artifact.instructionPC 2678 = 3469 := by
  rw [show (2678:Nat)=2671+(2678-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4005 : CycleSubmission.Artifact.artifact.instructionPC 2679 = 3472 := by
  rw [show (2679:Nat)=2671+(2679-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4006 : CycleSubmission.Artifact.artifact.instructionPC 2680 = 3473 := by
  rw [show (2680:Nat)=2671+(2680-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4007 : CycleSubmission.Artifact.artifact.instructionPC 2681 = 3475 := by
  rw [show (2681:Nat)=2671+(2681-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4008 : CycleSubmission.Artifact.artifact.instructionPC 2682 = 3476 := by
  rw [show (2682:Nat)=2671+(2682-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4009 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3477 := by
  rw [show (2683:Nat)=2671+(2683-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4010 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3478 := by
  rw [show (2684:Nat)=2671+(2684-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4011 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3479 := by
  rw [show (2685:Nat)=2671+(2685-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem fixedPC4012 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3482 := by
  rw [show (2686:Nat)=2671+(2686-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2883 : CycleSubmission.Artifact.artifact.instructionPC 2667 = 3454 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : CycleSubmission.Artifact.artifact.instructionPC 2668 = 3455 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : CycleSubmission.Artifact.artifact.instructionPC 2669 = 3456 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : CycleSubmission.Artifact.artifact.instructionPC 2670 = 3457 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : CycleSubmission.Artifact.artifact.instructionPC 2671 = 3458 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : CycleSubmission.Artifact.artifact.instructionPC 2672 = 3459 := by
  rw [show (2672:Nat)=2671+(2672-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2890 : CycleSubmission.Artifact.artifact.instructionPC 2673 = 3460 := by
  rw [show (2673:Nat)=2671+(2673-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2891 : CycleSubmission.Artifact.artifact.instructionPC 2674 = 3463 := by
  rw [show (2674:Nat)=2671+(2674-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2892 : CycleSubmission.Artifact.artifact.instructionPC 2675 = 3464 := by
  rw [show (2675:Nat)=2671+(2675-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2893 : CycleSubmission.Artifact.artifact.instructionPC 2675 = 3464 := by
  rw [show (2675:Nat)=2671+(2675-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2894 : CycleSubmission.Artifact.artifact.instructionPC 2676 = 3467 := by
  rw [show (2676:Nat)=2671+(2676-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2934 : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3468 := by
  rw [show (2677:Nat)=2671+(2677-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2935 : CycleSubmission.Artifact.artifact.instructionPC 2678 = 3469 := by
  rw [show (2678:Nat)=2671+(2678-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2936 : CycleSubmission.Artifact.artifact.instructionPC 2679 = 3472 := by
  rw [show (2679:Nat)=2671+(2679-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2937 : CycleSubmission.Artifact.artifact.instructionPC 2680 = 3473 := by
  rw [show (2680:Nat)=2671+(2680-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2938 : CycleSubmission.Artifact.artifact.instructionPC 2681 = 3475 := by
  rw [show (2681:Nat)=2671+(2681-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2939 : CycleSubmission.Artifact.artifact.instructionPC 2682 = 3476 := by
  rw [show (2682:Nat)=2671+(2682-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2940 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3477 := by
  rw [show (2683:Nat)=2671+(2683-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2941 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3478 := by
  rw [show (2684:Nat)=2671+(2684-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2942 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3479 := by
  rw [show (2685:Nat)=2671+(2685-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC2943 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3482 := by
  rw [show (2686:Nat)=2671+(2686-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3925 : CycleSubmission.Artifact.artifact.instructionPC 2852 = 3706 := by
  rw [show (2852:Nat)=2671+(2852-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3926 : CycleSubmission.Artifact.artifact.instructionPC 2853 = 3707 := by
  rw [show (2853:Nat)=2671+(2853-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3927 : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3710 := by
  rw [show (2854:Nat)=2671+(2854-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

@[simp] theorem earlyExtraPC3928 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3713 := by
  rw [show (2855:Nat)=2671+(2855-2671) from rfl, CycleSubmission.Global.PrefixPC.pc_add, cycleAnchor]
  rfl

end CycleSubmission.Global.Fast
