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
  [opAt 2830 .JUMPDEST,
   opAt 2831 .CALLDATASIZE,
   pushAt 2832 2 1000,
   opAt 2833 .EQ,
   pushAt 2834 2 4828,
   opAt 2835 .JUMPI]

def sizeFallbackPath : List Located :=
  [pushAt 2836 2 4766,
   opAt 2837 .JUMP]

def checkEntryPath : List Located :=
  [opAt 2838 .JUMPDEST,
   pushAt 2839 0 0,
   opAt 2840 .CALLDATALOAD,
   opAt 2841 (.Dup ⟨0, by decide⟩),
   pushAt 2842 8 7016996765293437281,
   opAt 2843 (.Dup ⟨0, by decide⟩),
   pushAt 2844 1 64,
   opAt 2845 .SHL,
   opAt 2846 .OR,
   opAt 2847 (.Dup ⟨0, by decide⟩),
   pushAt 2848 1 128,
   opAt 2849 .SHL,
   opAt 2850 .OR,
   opAt 2851 .XOR,
   pushAt 2852 1 32]

def loopPath : List Located :=
  [opAt 2853 .JUMPDEST,
   opAt 2854 (.Dup ⟨0, by decide⟩),
   opAt 2855 .CALLDATALOAD,
   opAt 2856 (.Dup ⟨3, by decide⟩),
   opAt 2857 .XOR,
   opAt 2858 (.Swap ⟨0, by decide⟩),
   opAt 2859 (.Swap ⟨1, by decide⟩),
   opAt 2860 .OR,
   opAt 2861 (.Swap ⟨0, by decide⟩),
   pushAt 2862 1 32,
   opAt 2863 .ADD,
   pushAt 2864 2 992,
   opAt 2865 (.Dup ⟨1, by decide⟩),
   opAt 2866 .LT,
   pushAt 2867 2 4854,
   opAt 2868 .JUMPI]

def tailPath : List Located :=
  [opAt 2869 .POP,
   pushAt 2870 2 992,
   opAt 2871 .CALLDATALOAD,
   pushAt 2872 1 192,
   opAt 2873 .SHR,
   opAt 2874 (.Dup ⟨2, by decide⟩),
   pushAt 2875 1 192,
   opAt 2876 .SHR,
   opAt 2877 .XOR,
   opAt 2878 .OR,
   opAt 2879 (.Swap ⟨0, by decide⟩),
   opAt 2880 .POP,
   pushAt 2881 2 4766,
   opAt 2882 .JUMPI]

def bodyPath : List Located :=
  [opAt 2883 (.Dup ⟨2, by decide⟩),
   pushAt 2884 1 6,
   opAt 2885 .SHR,
   pushAt 2886 1 21,
   opAt 2887 .MUL,
   pushAt 2888 2 4958,
   opAt 2889 .ADD,
   pushAt 2890 1 20,
   opAt 2891 (.Swap ⟨0, by decide⟩),
   pushAt 2892 0 0,
   opAt 2893 .CODECOPY,
   pushAt 2894 0 0,
   opAt 2895 .MLOAD,
   pushAt 2896 1 224,
   opAt 2897 .SHR,
   pushAt 2898 1 32,
   opAt 2899 .MSTORE,
   pushAt 2900 1 4,
   opAt 2901 .MLOAD,
   pushAt 2902 1 224,
   opAt 2903 .SHR,
   pushAt 2904 1 64,
   opAt 2905 .MSTORE,
   pushAt 2906 1 8,
   opAt 2907 .MLOAD,
   pushAt 2908 1 224,
   opAt 2909 .SHR,
   pushAt 2910 1 96,
   opAt 2911 .MSTORE,
   pushAt 2912 1 12,
   opAt 2913 .MLOAD,
   pushAt 2914 1 224,
   opAt 2915 .SHR,
   pushAt 2916 1 128,
   opAt 2917 .MSTORE,
   pushAt 2918 1 16,
   opAt 2919 .MLOAD,
   pushAt 2920 1 224,
   opAt 2921 .SHR,
   pushAt 2922 1 160,
   opAt 2923 .MSTORE,
   opAt 2924 .POP,
   opAt 2925 .JUMP]

@[simp] theorem pc2813 : Artifact.submissionArtifact.instructionPC 2830 = 3644 := by rfl
@[simp] theorem pc2814 : Artifact.submissionArtifact.instructionPC 2831 = 3645 := by rfl
@[simp] theorem pc2815 : Artifact.submissionArtifact.instructionPC 2832 = 3646 := by rfl
@[simp] theorem pc2816 : Artifact.submissionArtifact.instructionPC 2833 = 3647 := by rfl
@[simp] theorem pc2817 : Artifact.submissionArtifact.instructionPC 2834 = 3648 := by rfl
@[simp] theorem pc2818 : Artifact.submissionArtifact.instructionPC 2835 = 3649 := by rfl
@[simp] theorem pc2819 : Artifact.submissionArtifact.instructionPC 2836 = 3650 := by rfl
@[simp] theorem pc2820 : Artifact.submissionArtifact.instructionPC 2837 = 3651 := by rfl
@[simp] theorem pc2821 : Artifact.submissionArtifact.instructionPC 2838 = 3653 := by rfl
@[simp] theorem pc2822 : Artifact.submissionArtifact.instructionPC 2839 = 3654 := by rfl
@[simp] theorem pc2823 : Artifact.submissionArtifact.instructionPC 2840 = 3655 := by rfl
@[simp] theorem pc2824 : Artifact.submissionArtifact.instructionPC 2841 = 3656 := by rfl
@[simp] theorem pc2825 : Artifact.submissionArtifact.instructionPC 2842 = 3657 := by rfl
@[simp] theorem pc2826 : Artifact.submissionArtifact.instructionPC 2843 = 3658 := by rfl
@[simp] theorem pc2827 : Artifact.submissionArtifact.instructionPC 2844 = 3659 := by rfl
@[simp] theorem pc2828 : Artifact.submissionArtifact.instructionPC 2845 = 3660 := by rfl
@[simp] theorem pc2829 : Artifact.submissionArtifact.instructionPC 2846 = 3661 := by rfl
@[simp] theorem pc2830 : Artifact.submissionArtifact.instructionPC 2847 = 3663 := by rfl
@[simp] theorem pc2831 : Artifact.submissionArtifact.instructionPC 2848 = 3664 := by rfl
@[simp] theorem pc2832 : Artifact.submissionArtifact.instructionPC 2849 = 3665 := by rfl
@[simp] theorem pc2833 : Artifact.submissionArtifact.instructionPC 2850 = 3667 := by rfl
@[simp] theorem pc2834 : Artifact.submissionArtifact.instructionPC 2851 = 3668 := by rfl
@[simp] theorem pc2835 : Artifact.submissionArtifact.instructionPC 2852 = 3669 := by rfl
@[simp] theorem pc2836 : Artifact.submissionArtifact.instructionPC 2853 = 3670 := by rfl
@[simp] theorem pc2837 : Artifact.submissionArtifact.instructionPC 2854 = 3671 := by rfl
@[simp] theorem pc2838 : Artifact.submissionArtifact.instructionPC 2855 = 3672 := by rfl
@[simp] theorem pc2839 : Artifact.submissionArtifact.instructionPC 2856 = 3673 := by rfl
@[simp] theorem pc2840 : Artifact.submissionArtifact.instructionPC 2857 = 3674 := by rfl
@[simp] theorem pc2841 : Artifact.submissionArtifact.instructionPC 2858 = 3675 := by rfl
@[simp] theorem pc2842 : Artifact.submissionArtifact.instructionPC 2859 = 3676 := by rfl
@[simp] theorem pc2843 : Artifact.submissionArtifact.instructionPC 2860 = 3677 := by rfl
@[simp] theorem pc2844 : Artifact.submissionArtifact.instructionPC 2861 = 3678 := by rfl
@[simp] theorem pc2845 : Artifact.submissionArtifact.instructionPC 2862 = 3679 := by rfl
@[simp] theorem pc2846 : Artifact.submissionArtifact.instructionPC 2863 = 3680 := by rfl
@[simp] theorem pc2847 : Artifact.submissionArtifact.instructionPC 2864 = 3681 := by rfl
@[simp] theorem pc2848 : Artifact.submissionArtifact.instructionPC 2865 = 3682 := by rfl
@[simp] theorem pc2849 : Artifact.submissionArtifact.instructionPC 2866 = 3683 := by rfl
@[simp] theorem pc2850 : Artifact.submissionArtifact.instructionPC 2867 = 3685 := by rfl
@[simp] theorem pc2851 : Artifact.submissionArtifact.instructionPC 2868 = 3686 := by rfl
@[simp] theorem pc2852 : Artifact.submissionArtifact.instructionPC 2869 = 3687 := by rfl
@[simp] theorem pc2853 : Artifact.submissionArtifact.instructionPC 2870 = 3688 := by rfl
@[simp] theorem pc2854 : Artifact.submissionArtifact.instructionPC 2871 = 3689 := by rfl
@[simp] theorem pc2855 : Artifact.submissionArtifact.instructionPC 2872 = 3690 := by rfl
@[simp] theorem pc2856 : Artifact.submissionArtifact.instructionPC 2873 = 3691 := by rfl
@[simp] theorem pc2857 : Artifact.submissionArtifact.instructionPC 2874 = 3692 := by rfl
@[simp] theorem pc2858 : Artifact.submissionArtifact.instructionPC 2875 = 3693 := by rfl
@[simp] theorem pc2859 : Artifact.submissionArtifact.instructionPC 2876 = 3695 := by rfl
@[simp] theorem pc2860 : Artifact.submissionArtifact.instructionPC 2877 = 3696 := by rfl
@[simp] theorem pc2861 : Artifact.submissionArtifact.instructionPC 2878 = 3697 := by rfl
@[simp] theorem pc2862 : Artifact.submissionArtifact.instructionPC 2879 = 3699 := by rfl
@[simp] theorem pc2863 : Artifact.submissionArtifact.instructionPC 2880 = 3700 := by rfl
@[simp] theorem pc2864 : Artifact.submissionArtifact.instructionPC 2881 = 3701 := by rfl
@[simp] theorem pc2865 : Artifact.submissionArtifact.instructionPC 2882 = 3702 := by rfl
@[simp] theorem pc2866 : Artifact.submissionArtifact.instructionPC 2883 = 3703 := by rfl
@[simp] theorem pc2867 : Artifact.submissionArtifact.instructionPC 2884 = 3704 := by rfl
@[simp] theorem pc2868 : Artifact.submissionArtifact.instructionPC 2885 = 3705 := by rfl
@[simp] theorem pc2869 : Artifact.submissionArtifact.instructionPC 2886 = 3706 := by rfl
@[simp] theorem pc2870 : Artifact.submissionArtifact.instructionPC 2887 = 3707 := by rfl
@[simp] theorem pc2871 : Artifact.submissionArtifact.instructionPC 2888 = 3708 := by rfl
@[simp] theorem pc2872 : Artifact.submissionArtifact.instructionPC 2889 = 3709 := by rfl
@[simp] theorem pc2873 : Artifact.submissionArtifact.instructionPC 2890 = 3710 := by rfl
@[simp] theorem pc2874 : Artifact.submissionArtifact.instructionPC 2891 = 3711 := by rfl
@[simp] theorem pc2875 : Artifact.submissionArtifact.instructionPC 2892 = 3712 := by rfl
@[simp] theorem pc2876 : Artifact.submissionArtifact.instructionPC 2893 = 3713 := by rfl
@[simp] theorem pc2877 : Artifact.submissionArtifact.instructionPC 2894 = 3714 := by rfl
@[simp] theorem pc2878 : Artifact.submissionArtifact.instructionPC 2895 = 3715 := by rfl
@[simp] theorem pc2879 : Artifact.submissionArtifact.instructionPC 2896 = 3717 := by rfl
@[simp] theorem pc2880 : Artifact.submissionArtifact.instructionPC 2897 = 3718 := by rfl
@[simp] theorem pc2881 : Artifact.submissionArtifact.instructionPC 2898 = 3719 := by rfl
@[simp] theorem pc2882 : Artifact.submissionArtifact.instructionPC 2899 = 3720 := by rfl
@[simp] theorem pc2883 : Artifact.submissionArtifact.instructionPC 2900 = 3721 := by rfl
@[simp] theorem pc2884 : Artifact.submissionArtifact.instructionPC 2901 = 3722 := by rfl
@[simp] theorem pc2885 : Artifact.submissionArtifact.instructionPC 2902 = 3723 := by rfl
@[simp] theorem pc2886 : Artifact.submissionArtifact.instructionPC 2903 = 3724 := by rfl
@[simp] theorem pc2887 : Artifact.submissionArtifact.instructionPC 2904 = 3725 := by rfl
@[simp] theorem pc2888 : Artifact.submissionArtifact.instructionPC 2905 = 3727 := by rfl
@[simp] theorem pc2889 : Artifact.submissionArtifact.instructionPC 2906 = 3728 := by rfl
@[simp] theorem pc2890 : Artifact.submissionArtifact.instructionPC 2907 = 3729 := by rfl
@[simp] theorem pc2891 : Artifact.submissionArtifact.instructionPC 2908 = 3731 := by rfl
@[simp] theorem pc2892 : Artifact.submissionArtifact.instructionPC 2909 = 3732 := by rfl
@[simp] theorem pc2893 : Artifact.submissionArtifact.instructionPC 2910 = 3733 := by rfl
@[simp] theorem pc2894 : Artifact.submissionArtifact.instructionPC 2911 = 3734 := by rfl
@[simp] theorem pc2895 : Artifact.submissionArtifact.instructionPC 2912 = 3735 := by rfl
@[simp] theorem pc2896 : Artifact.submissionArtifact.instructionPC 2913 = 3736 := by rfl
@[simp] theorem pc2897 : Artifact.submissionArtifact.instructionPC 2914 = 3737 := by rfl
@[simp] theorem pc2898 : Artifact.submissionArtifact.instructionPC 2915 = 3738 := by rfl
@[simp] theorem pc2899 : Artifact.submissionArtifact.instructionPC 2916 = 3739 := by rfl
@[simp] theorem pc2900 : Artifact.submissionArtifact.instructionPC 2917 = 3740 := by rfl
@[simp] theorem pc2901 : Artifact.submissionArtifact.instructionPC 2918 = 3741 := by rfl
@[simp] theorem pc2902 : Artifact.submissionArtifact.instructionPC 2919 = 3742 := by rfl
@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2920 = 3743 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2921 = 3744 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2922 = 3745 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2923 = 3746 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2924 = 3747 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2925 = 3749 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths
