import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths

open EvmSemantics EvmSemantics.EVM

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def sizePath : List Located :=
  [opAt 2827 .JUMPDEST,
   opAt 2828 .CALLDATASIZE,
   pushAt 2829 2 1000,
   opAt 2830 .EQ,
   pushAt 2831 2 4823,
   opAt 2832 .JUMPI]

def sizeFallbackPath : List Located :=
  [pushAt 2833 2 4761,
   opAt 2834 .JUMP]

def checkEntryPath : List Located :=
  [opAt 2835 .JUMPDEST,
   pushAt 2836 0 0,
   opAt 2837 .CALLDATALOAD,
   opAt 2838 (.Dup ⟨0, by decide⟩),
   pushAt 2839 8 7016996765293437276,
   opAt 2840 (.Dup ⟨0, by decide⟩),
   pushAt 2841 1 64,
   opAt 2842 .SHL,
   opAt 2843 .OR,
   opAt 2844 (.Dup ⟨0, by decide⟩),
   pushAt 2845 1 128,
   opAt 2846 .SHL,
   opAt 2847 .OR,
   opAt 2848 .XOR,
   pushAt 2849 1 32]

def loopPath : List Located :=
  [opAt 2850 .JUMPDEST,
   opAt 2851 (.Dup ⟨0, by decide⟩),
   opAt 2852 .CALLDATALOAD,
   opAt 2853 (.Dup ⟨3, by decide⟩),
   opAt 2854 .XOR,
   opAt 2855 (.Swap ⟨0, by decide⟩),
   opAt 2856 (.Swap ⟨1, by decide⟩),
   opAt 2857 .OR,
   opAt 2858 (.Swap ⟨0, by decide⟩),
   pushAt 2859 1 32,
   opAt 2860 .ADD,
   pushAt 2861 2 992,
   opAt 2862 (.Dup ⟨1, by decide⟩),
   opAt 2863 .LT,
   pushAt 2864 2 4849,
   opAt 2865 .JUMPI]

def tailPath : List Located :=
  [opAt 2866 .POP,
   pushAt 2867 2 992,
   opAt 2868 .CALLDATALOAD,
   pushAt 2869 1 192,
   opAt 2870 .SHR,
   opAt 2871 (.Dup ⟨2, by decide⟩),
   pushAt 2872 1 192,
   opAt 2873 .SHR,
   opAt 2874 .XOR,
   opAt 2875 .OR,
   opAt 2876 (.Swap ⟨0, by decide⟩),
   opAt 2877 .POP,
   pushAt 2878 2 4761,
   opAt 2879 .JUMPI]

def bodyPath : List Located :=
  [opAt 2880 (.Dup ⟨2, by decide⟩),
   pushAt 2881 1 6,
   opAt 2882 .SHR,
   pushAt 2883 1 21,
   opAt 2884 .MUL,
   pushAt 2885 2 4953,
   opAt 2886 .ADD,
   pushAt 2887 1 20,
   opAt 2888 (.Swap ⟨0, by decide⟩),
   pushAt 2889 0 0,
   opAt 2890 .CODECOPY,
   pushAt 2891 0 0,
   opAt 2892 .MLOAD,
   pushAt 2893 1 224,
   opAt 2894 .SHR,
   pushAt 2895 1 32,
   opAt 2896 .MSTORE,
   pushAt 2897 1 4,
   opAt 2898 .MLOAD,
   pushAt 2899 1 224,
   opAt 2900 .SHR,
   pushAt 2901 1 64,
   opAt 2902 .MSTORE,
   pushAt 2903 1 8,
   opAt 2904 .MLOAD,
   pushAt 2905 1 224,
   opAt 2906 .SHR,
   pushAt 2907 1 96,
   opAt 2908 .MSTORE,
   pushAt 2909 1 12,
   opAt 2910 .MLOAD,
   pushAt 2911 1 224,
   opAt 2912 .SHR,
   pushAt 2913 1 128,
   opAt 2914 .MSTORE,
   pushAt 2915 1 16,
   opAt 2916 .MLOAD,
   pushAt 2917 1 224,
   opAt 2918 .SHR,
   pushAt 2919 1 160,
   opAt 2920 .MSTORE,
   opAt 2921 .POP,
   opAt 2922 .JUMP]

@[simp] theorem pc2813 : Artifact.submissionArtifact.instructionPC 2827 = 3641 := by rfl
@[simp] theorem pc2814 : Artifact.submissionArtifact.instructionPC 2828 = 3642 := by rfl
@[simp] theorem pc2815 : Artifact.submissionArtifact.instructionPC 2829 = 3643 := by rfl
@[simp] theorem pc2816 : Artifact.submissionArtifact.instructionPC 2830 = 3644 := by rfl
@[simp] theorem pc2817 : Artifact.submissionArtifact.instructionPC 2831 = 3645 := by rfl
@[simp] theorem pc2818 : Artifact.submissionArtifact.instructionPC 2832 = 3646 := by rfl
@[simp] theorem pc2819 : Artifact.submissionArtifact.instructionPC 2833 = 3647 := by rfl
@[simp] theorem pc2820 : Artifact.submissionArtifact.instructionPC 2834 = 3648 := by rfl
@[simp] theorem pc2821 : Artifact.submissionArtifact.instructionPC 2835 = 3650 := by rfl
@[simp] theorem pc2822 : Artifact.submissionArtifact.instructionPC 2836 = 3651 := by rfl
@[simp] theorem pc2823 : Artifact.submissionArtifact.instructionPC 2837 = 3652 := by rfl
@[simp] theorem pc2824 : Artifact.submissionArtifact.instructionPC 2838 = 3653 := by rfl
@[simp] theorem pc2825 : Artifact.submissionArtifact.instructionPC 2839 = 3654 := by rfl
@[simp] theorem pc2826 : Artifact.submissionArtifact.instructionPC 2840 = 3655 := by rfl
@[simp] theorem pc2827 : Artifact.submissionArtifact.instructionPC 2841 = 3656 := by rfl
@[simp] theorem pc2828 : Artifact.submissionArtifact.instructionPC 2842 = 3657 := by rfl
@[simp] theorem pc2829 : Artifact.submissionArtifact.instructionPC 2843 = 3658 := by rfl
@[simp] theorem pc2830 : Artifact.submissionArtifact.instructionPC 2844 = 3660 := by rfl
@[simp] theorem pc2831 : Artifact.submissionArtifact.instructionPC 2845 = 3661 := by rfl
@[simp] theorem pc2832 : Artifact.submissionArtifact.instructionPC 2846 = 3662 := by rfl
@[simp] theorem pc2833 : Artifact.submissionArtifact.instructionPC 2847 = 3664 := by rfl
@[simp] theorem pc2834 : Artifact.submissionArtifact.instructionPC 2848 = 3665 := by rfl
@[simp] theorem pc2835 : Artifact.submissionArtifact.instructionPC 2849 = 3666 := by rfl
@[simp] theorem pc2836 : Artifact.submissionArtifact.instructionPC 2850 = 3667 := by rfl
@[simp] theorem pc2837 : Artifact.submissionArtifact.instructionPC 2851 = 3668 := by rfl
@[simp] theorem pc2838 : Artifact.submissionArtifact.instructionPC 2852 = 3669 := by rfl
@[simp] theorem pc2839 : Artifact.submissionArtifact.instructionPC 2853 = 3670 := by rfl
@[simp] theorem pc2840 : Artifact.submissionArtifact.instructionPC 2854 = 3671 := by rfl
@[simp] theorem pc2841 : Artifact.submissionArtifact.instructionPC 2855 = 3672 := by rfl
@[simp] theorem pc2842 : Artifact.submissionArtifact.instructionPC 2856 = 3673 := by rfl
@[simp] theorem pc2843 : Artifact.submissionArtifact.instructionPC 2857 = 3674 := by rfl
@[simp] theorem pc2844 : Artifact.submissionArtifact.instructionPC 2858 = 3675 := by rfl
@[simp] theorem pc2845 : Artifact.submissionArtifact.instructionPC 2859 = 3676 := by rfl
@[simp] theorem pc2846 : Artifact.submissionArtifact.instructionPC 2860 = 3677 := by rfl
@[simp] theorem pc2847 : Artifact.submissionArtifact.instructionPC 2861 = 3678 := by rfl
@[simp] theorem pc2848 : Artifact.submissionArtifact.instructionPC 2862 = 3679 := by rfl
@[simp] theorem pc2849 : Artifact.submissionArtifact.instructionPC 2863 = 3680 := by rfl
@[simp] theorem pc2850 : Artifact.submissionArtifact.instructionPC 2864 = 3682 := by rfl
@[simp] theorem pc2851 : Artifact.submissionArtifact.instructionPC 2865 = 3683 := by rfl
@[simp] theorem pc2852 : Artifact.submissionArtifact.instructionPC 2866 = 3684 := by rfl
@[simp] theorem pc2853 : Artifact.submissionArtifact.instructionPC 2867 = 3685 := by rfl
@[simp] theorem pc2854 : Artifact.submissionArtifact.instructionPC 2868 = 3686 := by rfl
@[simp] theorem pc2855 : Artifact.submissionArtifact.instructionPC 2869 = 3687 := by rfl
@[simp] theorem pc2856 : Artifact.submissionArtifact.instructionPC 2870 = 3688 := by rfl
@[simp] theorem pc2857 : Artifact.submissionArtifact.instructionPC 2871 = 3689 := by rfl
@[simp] theorem pc2858 : Artifact.submissionArtifact.instructionPC 2872 = 3690 := by rfl
@[simp] theorem pc2859 : Artifact.submissionArtifact.instructionPC 2873 = 3692 := by rfl
@[simp] theorem pc2860 : Artifact.submissionArtifact.instructionPC 2874 = 3693 := by rfl
@[simp] theorem pc2861 : Artifact.submissionArtifact.instructionPC 2875 = 3694 := by rfl
@[simp] theorem pc2862 : Artifact.submissionArtifact.instructionPC 2876 = 3696 := by rfl
@[simp] theorem pc2863 : Artifact.submissionArtifact.instructionPC 2877 = 3697 := by rfl
@[simp] theorem pc2864 : Artifact.submissionArtifact.instructionPC 2878 = 3698 := by rfl
@[simp] theorem pc2865 : Artifact.submissionArtifact.instructionPC 2879 = 3699 := by rfl
@[simp] theorem pc2866 : Artifact.submissionArtifact.instructionPC 2880 = 3700 := by rfl
@[simp] theorem pc2867 : Artifact.submissionArtifact.instructionPC 2881 = 3701 := by rfl
@[simp] theorem pc2868 : Artifact.submissionArtifact.instructionPC 2882 = 3702 := by rfl
@[simp] theorem pc2869 : Artifact.submissionArtifact.instructionPC 2883 = 3703 := by rfl
@[simp] theorem pc2870 : Artifact.submissionArtifact.instructionPC 2884 = 3704 := by rfl
@[simp] theorem pc2871 : Artifact.submissionArtifact.instructionPC 2885 = 3705 := by rfl
@[simp] theorem pc2872 : Artifact.submissionArtifact.instructionPC 2886 = 3706 := by rfl
@[simp] theorem pc2873 : Artifact.submissionArtifact.instructionPC 2887 = 3707 := by rfl
@[simp] theorem pc2874 : Artifact.submissionArtifact.instructionPC 2888 = 3708 := by rfl
@[simp] theorem pc2875 : Artifact.submissionArtifact.instructionPC 2889 = 3709 := by rfl
@[simp] theorem pc2876 : Artifact.submissionArtifact.instructionPC 2890 = 3710 := by rfl
@[simp] theorem pc2877 : Artifact.submissionArtifact.instructionPC 2891 = 3711 := by rfl
@[simp] theorem pc2878 : Artifact.submissionArtifact.instructionPC 2892 = 3712 := by rfl
@[simp] theorem pc2879 : Artifact.submissionArtifact.instructionPC 2893 = 3714 := by rfl
@[simp] theorem pc2880 : Artifact.submissionArtifact.instructionPC 2894 = 3715 := by rfl
@[simp] theorem pc2881 : Artifact.submissionArtifact.instructionPC 2895 = 3716 := by rfl
@[simp] theorem pc2882 : Artifact.submissionArtifact.instructionPC 2896 = 3717 := by rfl
@[simp] theorem pc2883 : Artifact.submissionArtifact.instructionPC 2897 = 3718 := by rfl
@[simp] theorem pc2884 : Artifact.submissionArtifact.instructionPC 2898 = 3719 := by rfl
@[simp] theorem pc2885 : Artifact.submissionArtifact.instructionPC 2899 = 3720 := by rfl
@[simp] theorem pc2886 : Artifact.submissionArtifact.instructionPC 2900 = 3721 := by rfl
@[simp] theorem pc2887 : Artifact.submissionArtifact.instructionPC 2901 = 3722 := by rfl
@[simp] theorem pc2888 : Artifact.submissionArtifact.instructionPC 2902 = 3724 := by rfl
@[simp] theorem pc2889 : Artifact.submissionArtifact.instructionPC 2903 = 3725 := by rfl
@[simp] theorem pc2890 : Artifact.submissionArtifact.instructionPC 2904 = 3726 := by rfl
@[simp] theorem pc2891 : Artifact.submissionArtifact.instructionPC 2905 = 3728 := by rfl
@[simp] theorem pc2892 : Artifact.submissionArtifact.instructionPC 2906 = 3729 := by rfl
@[simp] theorem pc2893 : Artifact.submissionArtifact.instructionPC 2907 = 3730 := by rfl
@[simp] theorem pc2894 : Artifact.submissionArtifact.instructionPC 2908 = 3731 := by rfl
@[simp] theorem pc2895 : Artifact.submissionArtifact.instructionPC 2909 = 3732 := by rfl
@[simp] theorem pc2896 : Artifact.submissionArtifact.instructionPC 2910 = 3733 := by rfl
@[simp] theorem pc2897 : Artifact.submissionArtifact.instructionPC 2911 = 3734 := by rfl
@[simp] theorem pc2898 : Artifact.submissionArtifact.instructionPC 2912 = 3735 := by rfl
@[simp] theorem pc2899 : Artifact.submissionArtifact.instructionPC 2913 = 3736 := by rfl
@[simp] theorem pc2900 : Artifact.submissionArtifact.instructionPC 2914 = 3737 := by rfl
@[simp] theorem pc2901 : Artifact.submissionArtifact.instructionPC 2915 = 3738 := by rfl
@[simp] theorem pc2902 : Artifact.submissionArtifact.instructionPC 2916 = 3739 := by rfl
@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2917 = 3740 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2918 = 3741 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2919 = 3742 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2920 = 3743 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2921 = 3744 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2922 = 3746 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths
