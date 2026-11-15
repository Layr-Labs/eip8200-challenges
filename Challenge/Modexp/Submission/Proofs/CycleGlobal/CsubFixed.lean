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
    List.take_add_one,hget,Option.toList_some,assembleBytes_append,
    assembleBytes_cons,assembleBytes_nil,List.append_nil,List.length_append]
def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 690 2 2688,
   opAt 691 .MLOAD,
   pushAt 692 1 128,
   opAt 693 .EQ,
   pushAt 694 2 6622,
   opAt 695 .JUMPI]
def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 690 2 2688,
   opAt 691 .MLOAD,
   pushAt 692 1 128,
   opAt 693 .EQ,
   pushAt 694 2 6622,
   opAt 695 .JUMPI,
   opAt 4851 .JUMPDEST]
/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4608), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 696 2 2336,
   opAt 697 .MLOAD,
   pushAt 698 1 224,
   opAt 699 .MLOAD,
   opAt 700 (.Dup ⟨0,by decide⟩),
   opAt 701 (.Dup ⟨2,by decide⟩),
   opAt 702 .SUB,
   pushAt 703 2 2016,
   opAt 704 .MSTORE,
   opAt 705 .GT]
def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 706 (.Dup ⟨0,by decide⟩),
   pushAt 707 1 192,
   opAt 708 .MLOAD,
   opAt 709 .ADD,
   opAt 710 (.Dup ⟨0,by decide⟩),
   pushAt 711 2 2304,
   opAt 712 .MLOAD,
   opAt 713 (.Dup ⟨1,by decide⟩),
   opAt 714 (.Dup ⟨1,by decide⟩),
   opAt 715 .SUB,
   pushAt 716 2 1984,
   opAt 717 .MSTORE,
   opAt 718 .LT,
   opAt 719 (.Swap ⟨1,by decide⟩),
   opAt 720 .GT,
   opAt 721 .OR]
def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 722 (.Dup ⟨0,by decide⟩),
   pushAt 723 1 160,
   opAt 724 .MLOAD,
   opAt 725 .ADD,
   opAt 726 (.Dup ⟨0,by decide⟩),
   pushAt 727 2 2272,
   opAt 728 .MLOAD,
   opAt 729 (.Dup ⟨1,by decide⟩),
   opAt 730 (.Dup ⟨1,by decide⟩),
   opAt 731 .SUB,
   pushAt 732 2 1952,
   opAt 733 .MSTORE,
   opAt 734 .LT,
   opAt 735 (.Swap ⟨1,by decide⟩),
   opAt 736 .GT,
   opAt 737 .OR]
def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 738 (.Dup ⟨0,by decide⟩),
   pushAt 739 1 128,
   opAt 740 .MLOAD,
   opAt 741 .ADD,
   opAt 742 (.Dup ⟨0,by decide⟩),
   pushAt 743 2 2240,
   opAt 744 .MLOAD,
   opAt 745 (.Dup ⟨1,by decide⟩),
   opAt 746 (.Dup ⟨1,by decide⟩),
   opAt 747 .SUB,
   pushAt 748 2 1920,
   opAt 749 .MSTORE,
   opAt 750 .LT,
   opAt 751 (.Swap ⟨1,by decide⟩),
   opAt 752 .GT,
   opAt 753 .OR]
def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 754 (.Dup ⟨0,by decide⟩),
   pushAt 755 1 96,
   opAt 756 .MLOAD,
   opAt 757 .ADD,
   opAt 758 (.Dup ⟨0,by decide⟩),
   pushAt 759 2 2208,
   opAt 760 .MLOAD,
   opAt 761 (.Dup ⟨1,by decide⟩),
   opAt 762 (.Dup ⟨1,by decide⟩),
   opAt 763 .SUB,
   pushAt 764 2 1888,
   opAt 765 .MSTORE,
   opAt 766 .LT,
   opAt 767 (.Swap ⟨1,by decide⟩),
   opAt 768 .GT,
   opAt 769 .OR]
def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 770 .JUMPDEST,
   opAt 771 (.Dup ⟨0,by decide⟩),
   pushAt 772 1 64,
   opAt 773 .MLOAD,
   opAt 774 .ADD,
   opAt 775 (.Dup ⟨0,by decide⟩),
   pushAt 776 2 2176,
   opAt 777 .MLOAD,
   opAt 778 (.Dup ⟨1,by decide⟩),
   opAt 779 (.Dup ⟨1,by decide⟩),
   opAt 780 .SUB,
   pushAt 781 2 1856,
   opAt 782 .MSTORE,
   opAt 783 .LT,
   opAt 784 (.Swap ⟨1,by decide⟩),
   opAt 785 .GT,
   opAt 786 .OR]
def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 787 (.Dup ⟨0,by decide⟩),
   pushAt 788 1 32,
   opAt 789 .MLOAD,
   opAt 790 .ADD,
   opAt 791 (.Dup ⟨0,by decide⟩),
   pushAt 792 2 2144,
   opAt 793 .MLOAD,
   opAt 794 (.Dup ⟨1,by decide⟩),
   opAt 795 (.Dup ⟨1,by decide⟩),
   opAt 796 .SUB,
   pushAt 797 2 1824,
   opAt 798 .MSTORE,
   opAt 799 .LT,
   opAt 800 (.Swap ⟨1,by decide⟩),
   opAt 801 .GT,
   opAt 802 .OR]
def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 803 (.Dup ⟨0,by decide⟩),
   pushAt 804 0 0,
   opAt 805 .MLOAD,
   opAt 806 .ADD,
   opAt 807 (.Dup ⟨0,by decide⟩),
   pushAt 808 2 2112,
   opAt 809 .MLOAD,
   opAt 810 (.Dup ⟨1,by decide⟩),
   opAt 811 (.Dup ⟨1,by decide⟩),
   opAt 812 .SUB,
   pushAt 813 2 1792,
   opAt 814 .MSTORE,
   opAt 815 .LT,
   opAt 816 (.Swap ⟨1,by decide⟩),
   opAt 817 .GT,
   opAt 818 .OR]
/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 2526, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 819 .ISZERO,
   pushAt 820 2 2080,
   opAt 821 .MLOAD,
   opAt 822 .OR,
   pushAt 823 2 1143,
   opAt 824 .JUMPI,
   opAt 834 .JUMPDEST,
   pushAt 835 2 1792,
   pushAt 836 2 2688,
   opAt 837 .MLOAD,
   opAt 838 (.Swap ⟨1,by decide⟩),
   opAt 839 .MCOPY,
   opAt 840 .JUMP]
/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 2515, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 819 .ISZERO,
   pushAt 820 2 2080,
   opAt 821 .MLOAD,
   opAt 822 .OR,
   pushAt 823 2 1143,
   opAt 824 .JUMPI,
   pushAt 825 2 1132,
   opAt 826 .JUMP,
   opAt 827 .JUMPDEST,
   pushAt 828 2 2112,
   pushAt 829 2 2688,
   opAt 830 .MLOAD,
   opAt 831 (.Swap ⟨1,by decide⟩),
   opAt 832 .MCOPY,
   opAt 833 .JUMP]
def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 4852 2 2208,
   opAt 4853 .MLOAD,
   pushAt 4854 1 96,
   opAt 4855 .MLOAD,
   opAt 4856 (.Dup ⟨0,by decide⟩),
   opAt 4857 (.Dup ⟨2,by decide⟩),
   opAt 4858 .SUB,
   pushAt 4859 2 1888,
   opAt 4860 .MSTORE,
   opAt 4861 .GT,
   pushAt 4862 2 1055,
   opAt 4863 .JUMP]
def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 770 .JUMPDEST,
   opAt 771 (.Dup ⟨0,by decide⟩),
   pushAt 772 1 64,
   opAt 773 .MLOAD,
   opAt 774 .ADD,
   opAt 775 (.Dup ⟨0,by decide⟩),
   pushAt 776 2 2176,
   opAt 777 .MLOAD,
   opAt 778 (.Dup ⟨1,by decide⟩),
   opAt 779 (.Dup ⟨1,by decide⟩),
   opAt 780 .SUB,
   pushAt 781 2 1856,
   opAt 782 .MSTORE,
   opAt 783 .LT,
   opAt 784 (.Swap ⟨1,by decide⟩),
   opAt 785 .GT,
   opAt 786 .OR]
def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 787 (.Dup ⟨0,by decide⟩),
   pushAt 788 1 32,
   opAt 789 .MLOAD,
   opAt 790 .ADD,
   opAt 791 (.Dup ⟨0,by decide⟩),
   pushAt 792 2 2144,
   opAt 793 .MLOAD,
   opAt 794 (.Dup ⟨1,by decide⟩),
   opAt 795 (.Dup ⟨1,by decide⟩),
   opAt 796 .SUB,
   pushAt 797 2 1824,
   opAt 798 .MSTORE,
   opAt 799 .LT,
   opAt 800 (.Swap ⟨1,by decide⟩),
   opAt 801 .GT,
   opAt 802 .OR]
def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 803 (.Dup ⟨0,by decide⟩),
   pushAt 804 0 0,
   opAt 805 .MLOAD,
   opAt 806 .ADD,
   opAt 807 (.Dup ⟨0,by decide⟩),
   pushAt 808 2 2112,
   opAt 809 .MLOAD,
   opAt 810 (.Dup ⟨1,by decide⟩),
   opAt 811 (.Dup ⟨1,by decide⟩),
   opAt 812 .SUB,
   pushAt 813 2 1792,
   opAt 814 .MSTORE,
   opAt 815 .LT,
   opAt 816 (.Swap ⟨1,by decide⟩),
   opAt 817 .GT,
   opAt 818 .OR]
@[simp] theorem cycleAnchor : runtimeArtifact.instructionPC 8171 = 10844 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3777 : runtimeArtifact.instructionPC 685 = 934 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3778 : runtimeArtifact.instructionPC 825 = 1128 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3779 : runtimeArtifact.instructionPC 826 = 1131 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3787 : runtimeArtifact.instructionPC 827 = 1132 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3788 : runtimeArtifact.instructionPC 827 = 1132 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3789 : runtimeArtifact.instructionPC 827 = 1132 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3790 : runtimeArtifact.instructionPC 827 = 1132 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3791 : runtimeArtifact.instructionPC 827 = 1132 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3792 : runtimeArtifact.instructionPC 827 = 1132 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3793 : runtimeArtifact.instructionPC 828 = 1133 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3794 : runtimeArtifact.instructionPC 829 = 1136 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3795 : runtimeArtifact.instructionPC 830 = 1139 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3796 : runtimeArtifact.instructionPC 831 = 1140 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3797 : runtimeArtifact.instructionPC 832 = 1141 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3798 : runtimeArtifact.instructionPC 832 = 1141 := fixedPC3797
@[simp] theorem fixedPC3799 : runtimeArtifact.instructionPC 832 = 1141 := fixedPC3797
@[simp] theorem fixedPC3800 : runtimeArtifact.instructionPC 833 = 1142 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3801 : runtimeArtifact.instructionPC 834 = 1143 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3802 : runtimeArtifact.instructionPC 835 = 1144 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3803 : runtimeArtifact.instructionPC 836 = 1147 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3804 : runtimeArtifact.instructionPC 837 = 1150 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : runtimeArtifact.instructionPC 686 = 935 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3115 : runtimeArtifact.instructionPC 687 = 938 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3116 : runtimeArtifact.instructionPC 688 = 939 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3117 : runtimeArtifact.instructionPC 689 = 942 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3118 : runtimeArtifact.instructionPC 690 = 945 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3119 : runtimeArtifact.instructionPC 691 = 948 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 2359 through index 1261, which is now an `MCOPY` at 2380, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : runtimeArtifact.instructionPC 8177 = 10853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 6622 = true := by
  have h : runtimeArtifact.instructionPC 4851 = 6622 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 4851 (by rfl)
@[simp] theorem fixedPC3805 : runtimeArtifact.instructionPC 692 = 949 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3806 : runtimeArtifact.instructionPC 693 = 951 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3807 : runtimeArtifact.instructionPC 694 = 952 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3808 : runtimeArtifact.instructionPC 695 = 955 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPCs8 : runtimeArtifact.instructionPC 696 = 956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3809 : runtimeArtifact.instructionPC 696 = 956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3810 : runtimeArtifact.instructionPC 697 = 959 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3811 : runtimeArtifact.instructionPC 698 = 960 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3812 : runtimeArtifact.instructionPC 699 = 962 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3813 : runtimeArtifact.instructionPC 700 = 963 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3814 : runtimeArtifact.instructionPC 701 = 964 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3815 : runtimeArtifact.instructionPC 702 = 965 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3816 : runtimeArtifact.instructionPC 702 = 965 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3817 : runtimeArtifact.instructionPC 703 = 966 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3818 : runtimeArtifact.instructionPC 704 = 969 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3819 : runtimeArtifact.instructionPC 705 = 970 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3820 : runtimeArtifact.instructionPC 706 = 971 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3821 : runtimeArtifact.instructionPC 707 = 972 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3822 : runtimeArtifact.instructionPC 708 = 974 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3823 : runtimeArtifact.instructionPC 709 = 975 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3824 : runtimeArtifact.instructionPC 710 = 976 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3825 : runtimeArtifact.instructionPC 711 = 977 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3826 : runtimeArtifact.instructionPC 712 = 980 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3827 : runtimeArtifact.instructionPC 713 = 981 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3828 : runtimeArtifact.instructionPC 714 = 982 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3829 : runtimeArtifact.instructionPC 715 = 983 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3830 : runtimeArtifact.instructionPC 716 = 984 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3831 : runtimeArtifact.instructionPC 717 = 987 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3832 : runtimeArtifact.instructionPC 718 = 988 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3833 : runtimeArtifact.instructionPC 719 = 989 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3834 : runtimeArtifact.instructionPC 719 = 989 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3835 : runtimeArtifact.instructionPC 720 = 990 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3836 : runtimeArtifact.instructionPC 721 = 991 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3837 : runtimeArtifact.instructionPC 722 = 992 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3838 : runtimeArtifact.instructionPC 723 = 993 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3839 : runtimeArtifact.instructionPC 724 = 995 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3840 : runtimeArtifact.instructionPC 725 = 996 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3841 : runtimeArtifact.instructionPC 726 = 997 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3842 : runtimeArtifact.instructionPC 727 = 998 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3843 : runtimeArtifact.instructionPC 728 = 1001 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3844 : runtimeArtifact.instructionPC 729 = 1002 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3845 : runtimeArtifact.instructionPC 730 = 1003 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3846 : runtimeArtifact.instructionPC 731 = 1004 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3847 : runtimeArtifact.instructionPC 732 = 1005 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3848 : runtimeArtifact.instructionPC 733 = 1008 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3849 : runtimeArtifact.instructionPC 734 = 1009 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3850 : runtimeArtifact.instructionPC 735 = 1010 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3851 : runtimeArtifact.instructionPC 736 = 1011 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3852 : runtimeArtifact.instructionPC 736 = 1011 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3853 : runtimeArtifact.instructionPC 737 = 1012 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3854 : runtimeArtifact.instructionPC 738 = 1013 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3855 : runtimeArtifact.instructionPC 739 = 1014 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3856 : runtimeArtifact.instructionPC 740 = 1016 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3857 : runtimeArtifact.instructionPC 741 = 1017 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3858 : runtimeArtifact.instructionPC 742 = 1018 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3859 : runtimeArtifact.instructionPC 743 = 1019 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3860 : runtimeArtifact.instructionPC 744 = 1022 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3861 : runtimeArtifact.instructionPC 745 = 1023 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3862 : runtimeArtifact.instructionPC 746 = 1024 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3863 : runtimeArtifact.instructionPC 747 = 1025 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3864 : runtimeArtifact.instructionPC 748 = 1026 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3865 : runtimeArtifact.instructionPC 749 = 1029 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3866 : runtimeArtifact.instructionPC 750 = 1030 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3867 : runtimeArtifact.instructionPC 751 = 1031 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3868 : runtimeArtifact.instructionPC 752 = 1032 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3869 : runtimeArtifact.instructionPC 753 = 1033 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3871 : runtimeArtifact.instructionPC 753 = 1033 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3872 : runtimeArtifact.instructionPC 754 = 1034 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3873 : runtimeArtifact.instructionPC 755 = 1035 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3874 : runtimeArtifact.instructionPC 756 = 1037 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3875 : runtimeArtifact.instructionPC 757 = 1038 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3876 : runtimeArtifact.instructionPC 758 = 1039 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3877 : runtimeArtifact.instructionPC 759 = 1040 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3878 : runtimeArtifact.instructionPC 760 = 1043 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3879 : runtimeArtifact.instructionPC 761 = 1044 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3880 : runtimeArtifact.instructionPC 762 = 1045 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3881 : runtimeArtifact.instructionPC 763 = 1046 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3882 : runtimeArtifact.instructionPC 764 = 1047 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3883 : runtimeArtifact.instructionPC 765 = 1050 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3884 : runtimeArtifact.instructionPC 766 = 1051 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3885 : runtimeArtifact.instructionPC 767 = 1052 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3886 : runtimeArtifact.instructionPC 768 = 1053 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3887 : runtimeArtifact.instructionPC 769 = 1054 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3888 : runtimeArtifact.instructionPC 770 = 1055 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3889 : runtimeArtifact.instructionPC 770 = 1055 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 1055 = true := by
  have h : runtimeArtifact.instructionPC 770 = 1055 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 770 (by rfl)
@[simp] theorem fixedPC3890 : runtimeArtifact.instructionPC 771 = 1056 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3891 : runtimeArtifact.instructionPC 772 = 1057 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3892 : runtimeArtifact.instructionPC 773 = 1059 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3893 : runtimeArtifact.instructionPC 774 = 1060 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3894 : runtimeArtifact.instructionPC 775 = 1061 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3895 : runtimeArtifact.instructionPC 776 = 1062 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3896 : runtimeArtifact.instructionPC 777 = 1065 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3897 : runtimeArtifact.instructionPC 778 = 1066 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3898 : runtimeArtifact.instructionPC 779 = 1067 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3899 : runtimeArtifact.instructionPC 780 = 1068 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3900 : runtimeArtifact.instructionPC 781 = 1069 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3901 : runtimeArtifact.instructionPC 782 = 1072 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3902 : runtimeArtifact.instructionPC 783 = 1073 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3903 : runtimeArtifact.instructionPC 784 = 1074 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3904 : runtimeArtifact.instructionPC 785 = 1075 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3905 : runtimeArtifact.instructionPC 786 = 1076 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3906 : runtimeArtifact.instructionPC 787 = 1077 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3907 : runtimeArtifact.instructionPC 788 = 1078 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3908 : runtimeArtifact.instructionPC 788 = 1078 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3909 : runtimeArtifact.instructionPC 789 = 1080 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3910 : runtimeArtifact.instructionPC 790 = 1081 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3911 : runtimeArtifact.instructionPC 791 = 1082 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3912 : runtimeArtifact.instructionPC 792 = 1083 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3913 : runtimeArtifact.instructionPC 793 = 1086 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3914 : runtimeArtifact.instructionPC 794 = 1087 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3915 : runtimeArtifact.instructionPC 795 = 1088 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3916 : runtimeArtifact.instructionPC 796 = 1089 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3917 : runtimeArtifact.instructionPC 797 = 1090 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3918 : runtimeArtifact.instructionPC 798 = 1093 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3919 : runtimeArtifact.instructionPC 799 = 1094 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3920 : runtimeArtifact.instructionPC 800 = 1095 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3921 : runtimeArtifact.instructionPC 801 = 1096 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3922 : runtimeArtifact.instructionPC 802 = 1097 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3923 : runtimeArtifact.instructionPC 803 = 1098 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3924 : runtimeArtifact.instructionPC 804 = 1099 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3925 : runtimeArtifact.instructionPC 805 = 1100 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3926 : runtimeArtifact.instructionPC 805 = 1100 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3927 : runtimeArtifact.instructionPC 806 = 1101 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3928 : runtimeArtifact.instructionPC 807 = 1102 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3929 : runtimeArtifact.instructionPC 808 = 1103 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3930 : runtimeArtifact.instructionPC 809 = 1106 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3931 : runtimeArtifact.instructionPC 810 = 1107 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3932 : runtimeArtifact.instructionPC 811 = 1108 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3933 : runtimeArtifact.instructionPC 812 = 1109 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3934 : runtimeArtifact.instructionPC 813 = 1110 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3935 : runtimeArtifact.instructionPC 814 = 1113 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3936 : runtimeArtifact.instructionPC 815 = 1114 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3937 : runtimeArtifact.instructionPC 816 = 1115 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3938 : runtimeArtifact.instructionPC 817 = 1116 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3939 : runtimeArtifact.instructionPC 818 = 1117 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3940 : runtimeArtifact.instructionPC 819 = 1118 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3941 : runtimeArtifact.instructionPC 820 = 1119 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3942 : runtimeArtifact.instructionPC 821 = 1122 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3943 : runtimeArtifact.instructionPC 822 = 1123 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3944 : runtimeArtifact.instructionPC 822 = 1123 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3945 : runtimeArtifact.instructionPC 823 = 1124 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3946 : runtimeArtifact.instructionPC 824 = 1127 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3947 : runtimeArtifact.instructionPC 825 = 1128 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3948 : runtimeArtifact.instructionPC 826 = 1131 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3949 : runtimeArtifact.instructionPC 831 = 1140 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3950 : runtimeArtifact.instructionPC 831 = 1140 :=
  fixedPC3949
@[simp] theorem fixedPC3951 : runtimeArtifact.instructionPC 832 = 1141 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3952 : runtimeArtifact.instructionPC 833 = 1142 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3953 : runtimeArtifact.instructionPC 834 = 1143 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3954 : runtimeArtifact.instructionPC 835 = 1144 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3955 : runtimeArtifact.instructionPC 836 = 1147 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3956 : runtimeArtifact.instructionPC 837 = 1150 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3957 : runtimeArtifact.instructionPC 838 = 1151 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 6622 = true := by
  have h : runtimeArtifact.instructionPC 4851 = 6622 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 4851 (by rfl)
@[simp] theorem fixedPC4000 : runtimeArtifact.instructionPC 8177 = 10853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4001 : runtimeArtifact.instructionPC 8177 = 10853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4002 : runtimeArtifact.instructionPC 8196 = 10876 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4003 : runtimeArtifact.instructionPC 4851 = 6622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4004 : runtimeArtifact.instructionPC 4852 = 6623 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4005 : runtimeArtifact.instructionPC 4853 = 6626 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4006 : runtimeArtifact.instructionPC 4854 = 6627 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4007 : runtimeArtifact.instructionPC 4855 = 6629 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4008 : runtimeArtifact.instructionPC 4856 = 6630 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4009 : runtimeArtifact.instructionPC 4857 = 6631 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4010 : runtimeArtifact.instructionPC 4858 = 6632 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4011 : runtimeArtifact.instructionPC 4859 = 6633 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4012 : runtimeArtifact.instructionPC 4860 = 6636 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2883 : runtimeArtifact.instructionPC 7439 = 9897 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2884 : runtimeArtifact.instructionPC 7440 = 9898 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2885 : runtimeArtifact.instructionPC 7441 = 9899 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2886 : runtimeArtifact.instructionPC 7442 = 9900 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2888 : runtimeArtifact.instructionPC 7443 = 9901 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2889 : runtimeArtifact.instructionPC 7444 = 9902 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2890 : runtimeArtifact.instructionPC 7445 = 9903 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2891 : runtimeArtifact.instructionPC 7446 = 9906 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2892 : runtimeArtifact.instructionPC 7447 = 9907 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2893 : runtimeArtifact.instructionPC 7447 = 9907 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2894 : runtimeArtifact.instructionPC 7447 = 9907 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2895 : runtimeArtifact.instructionPC 8165 = 10834 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2896 : runtimeArtifact.instructionPC 8177 = 10853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2930 : runtimeArtifact.instructionPC 8177 = 10853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2931 : runtimeArtifact.instructionPC 8177 = 10853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2932 : runtimeArtifact.instructionPC 8177 = 10853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2933 : runtimeArtifact.instructionPC 8196 = 10876 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2934 : runtimeArtifact.instructionPC 4851 = 6622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2935 : runtimeArtifact.instructionPC 4852 = 6623 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2936 : runtimeArtifact.instructionPC 4853 = 6626 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2937 : runtimeArtifact.instructionPC 4854 = 6627 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2938 : runtimeArtifact.instructionPC 4855 = 6629 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2939 : runtimeArtifact.instructionPC 4856 = 6630 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2940 : runtimeArtifact.instructionPC 4857 = 6631 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2941 : runtimeArtifact.instructionPC 4858 = 6632 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2942 : runtimeArtifact.instructionPC 4859 = 6633 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2943 : runtimeArtifact.instructionPC 4860 = 6636 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3921 : runtimeArtifact.instructionPC 827 = 1132 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3922 : runtimeArtifact.instructionPC 827 = 1132 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3923 : runtimeArtifact.instructionPC 827 = 1132 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3924 : runtimeArtifact.instructionPC 827 = 1132 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3925 : runtimeArtifact.instructionPC 827 = 1132 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3926 : runtimeArtifact.instructionPC 828 = 1133 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3927 : runtimeArtifact.instructionPC 829 = 1136 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3928 : runtimeArtifact.instructionPC 830 = 1139 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
end CycleSubmission.Global.Fast
