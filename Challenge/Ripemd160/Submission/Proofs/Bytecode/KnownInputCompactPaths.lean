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
  [opAt 2809 .JUMPDEST,
   opAt 2810 .CALLDATASIZE,
   pushAt 2811 2 1000,
   opAt 2812 .EQ,
   pushAt 2813 2 4834,
   opAt 2814 .JUMPI]

def sizeFallbackPath : List Located :=
  [pushAt 2815 2 4772,
   opAt 2816 .JUMP]

def checkEntryPath : List Located :=
  [opAt 2817 .JUMPDEST,
   pushAt 2818 0 0,
   opAt 2819 .CALLDATALOAD,
   opAt 2820 (.Dup ⟨0, by decide⟩),
   pushAt 2821 8 7016996765293437281,
   opAt 2822 (.Dup ⟨0, by decide⟩),
   pushAt 2823 2 576,
   opAt 2824 .SHL,
   opAt 2825 .OR,
   opAt 2826 (.Dup ⟨0, by decide⟩),
   pushAt 2827 1 128,
   opAt 2828 .SHL,
   opAt 2829 .OR,
   opAt 2830 .XOR,
   pushAt 2831 1 32]

def loopPath : List Located :=
  [opAt 2832 .JUMPDEST,
   opAt 2833 (.Dup ⟨0, by decide⟩),
   opAt 2834 .CALLDATALOAD,
   opAt 2835 (.Dup ⟨3, by decide⟩),
   opAt 2836 .XOR,
   opAt 2837 (.Swap ⟨0, by decide⟩),
   opAt 2838 (.Swap ⟨1, by decide⟩),
   opAt 2839 .OR,
   opAt 2840 (.Swap ⟨0, by decide⟩),
   pushAt 2841 1 26,
   opAt 2842 .ADD,
   pushAt 2843 2 992,
   opAt 2844 (.Dup ⟨1, by decide⟩),
   opAt 2845 .LT,
   pushAt 2846 2 4860,
   opAt 2847 .JUMPI]

def tailPath : List Located :=
  [opAt 2848 .POP,
   pushAt 2849 2 992,
   opAt 2850 .CALLDATALOAD,
   pushAt 2851 1 192,
   opAt 2852 .SHR,
   opAt 2853 (.Dup ⟨2, by decide⟩),
   pushAt 2854 1 192,
   opAt 2855 .SHR,
   opAt 2856 .XOR,
   opAt 2857 .OR,
   opAt 2858 (.Swap ⟨0, by decide⟩),
   opAt 2859 .POP,
   pushAt 2860 2 4772,
   opAt 2861 .JUMPI]

def bodyPath : List Located :=
  [opAt 2862 (.Dup ⟨2, by decide⟩),
   pushAt 2863 1 6,
   opAt 2864 .SHR,
   pushAt 2865 1 21,
   opAt 2866 .MUL,
   pushAt 2867 2 4964,
   opAt 2868 .ADD,
   pushAt 2869 2 320,
   opAt 2870 (.Swap ⟨0, by decide⟩),
   pushAt 2871 1 208,
   opAt 2872 .CODECOPY,
   pushAt 2873 0 0,
   opAt 2874 .MLOAD,
   pushAt 2875 1 224,
   opAt 2876 .SHR,
   pushAt 2877 1 32,
   opAt 2878 .MSTORE,
   pushAt 2879 1 4,
   opAt 2880 .MLOAD,
   pushAt 2881 1 224,
   opAt 2882 .SHR,
   pushAt 2883 1 64,
   opAt 2884 .MSTORE,
   pushAt 2885 1 8,
   opAt 2886 .MLOAD,
   pushAt 2887 1 24,
   opAt 2888 .SHR,
   pushAt 2889 1 96,
   opAt 2890 .MSTORE,
   pushAt 2891 1 12,
   opAt 2892 .MLOAD,
   pushAt 2893 1 224,
   opAt 2894 .SHR,
   pushAt 2895 1 128,
   opAt 2896 .MSTORE,
   pushAt 2897 1 16,
   opAt 2898 .MLOAD,
   pushAt 2899 1 224,
   opAt 2900 .SHR,
   pushAt 2901 1 160,
   opAt 2902 .MSTORE,
   opAt 2903 .POP,
   opAt 2904 .JUMP]

@[simp] theorem pc2813 : Artifact.submissionArtifact.instructionPC 2827 = 3555 := by rfl
@[simp] theorem pc2814 : Artifact.submissionArtifact.instructionPC 2828 = 3556 := by rfl
@[simp] theorem pc2815 : Artifact.submissionArtifact.instructionPC 2829 = 3557 := by rfl
@[simp] theorem pc2816 : Artifact.submissionArtifact.instructionPC 2830 = 3558 := by rfl
@[simp] theorem pc2817 : Artifact.submissionArtifact.instructionPC 2831 = 3559 := by rfl
@[simp] theorem pc2818 : Artifact.submissionArtifact.instructionPC 2832 = 3560 := by rfl
@[simp] theorem pc2819 : Artifact.submissionArtifact.instructionPC 2833 = 3561 := by rfl
@[simp] theorem pc2820 : Artifact.submissionArtifact.instructionPC 2834 = 3562 := by rfl
@[simp] theorem pc2821 : Artifact.submissionArtifact.instructionPC 2835 = 3563 := by rfl
@[simp] theorem pc2822 : Artifact.submissionArtifact.instructionPC 2836 = 3564 := by rfl
@[simp] theorem pc2823 : Artifact.submissionArtifact.instructionPC 2837 = 3566 := by rfl
@[simp] theorem pc2824 : Artifact.submissionArtifact.instructionPC 2838 = 3567 := by rfl
@[simp] theorem pc2825 : Artifact.submissionArtifact.instructionPC 2839 = 3568 := by rfl
@[simp] theorem pc2826 : Artifact.submissionArtifact.instructionPC 2840 = 3569 := by rfl
@[simp] theorem pc2827 : Artifact.submissionArtifact.instructionPC 2841 = 3570 := by rfl
@[simp] theorem pc2828 : Artifact.submissionArtifact.instructionPC 2842 = 3572 := by rfl
@[simp] theorem pc2829 : Artifact.submissionArtifact.instructionPC 2843 = 3573 := by rfl
@[simp] theorem pc2830 : Artifact.submissionArtifact.instructionPC 2844 = 3574 := by rfl
@[simp] theorem pc2831 : Artifact.submissionArtifact.instructionPC 2845 = 3575 := by rfl
@[simp] theorem pc2832 : Artifact.submissionArtifact.instructionPC 2846 = 3576 := by rfl
@[simp] theorem pc2833 : Artifact.submissionArtifact.instructionPC 2847 = 3577 := by rfl
@[simp] theorem pc2834 : Artifact.submissionArtifact.instructionPC 2848 = 3578 := by rfl
@[simp] theorem pc2835 : Artifact.submissionArtifact.instructionPC 2849 = 3579 := by rfl
@[simp] theorem pc2836 : Artifact.submissionArtifact.instructionPC 2850 = 3580 := by rfl
@[simp] theorem pc2837 : Artifact.submissionArtifact.instructionPC 2851 = 3582 := by rfl
@[simp] theorem pc2838 : Artifact.submissionArtifact.instructionPC 2852 = 3583 := by rfl
@[simp] theorem pc2839 : Artifact.submissionArtifact.instructionPC 2853 = 3584 := by rfl
@[simp] theorem pc2840 : Artifact.submissionArtifact.instructionPC 2854 = 3585 := by rfl
@[simp] theorem pc2841 : Artifact.submissionArtifact.instructionPC 2855 = 3586 := by rfl
@[simp] theorem pc2842 : Artifact.submissionArtifact.instructionPC 2856 = 3587 := by rfl
@[simp] theorem pc2843 : Artifact.submissionArtifact.instructionPC 2857 = 3588 := by rfl
@[simp] theorem pc2844 : Artifact.submissionArtifact.instructionPC 2858 = 3589 := by rfl
@[simp] theorem pc2845 : Artifact.submissionArtifact.instructionPC 2859 = 3590 := by rfl
@[simp] theorem pc2846 : Artifact.submissionArtifact.instructionPC 2860 = 3591 := by rfl
@[simp] theorem pc2847 : Artifact.submissionArtifact.instructionPC 2861 = 3592 := by rfl
@[simp] theorem pc2848 : Artifact.submissionArtifact.instructionPC 2862 = 3593 := by rfl
@[simp] theorem pc2849 : Artifact.submissionArtifact.instructionPC 2863 = 3594 := by rfl
@[simp] theorem pc2850 : Artifact.submissionArtifact.instructionPC 2864 = 3595 := by rfl
@[simp] theorem pc2851 : Artifact.submissionArtifact.instructionPC 2865 = 3596 := by rfl
@[simp] theorem pc2852 : Artifact.submissionArtifact.instructionPC 2866 = 3597 := by rfl
@[simp] theorem pc2853 : Artifact.submissionArtifact.instructionPC 2867 = 3598 := by rfl
@[simp] theorem pc2854 : Artifact.submissionArtifact.instructionPC 2868 = 3599 := by rfl
@[simp] theorem pc2855 : Artifact.submissionArtifact.instructionPC 2869 = 3600 := by rfl
@[simp] theorem pc2856 : Artifact.submissionArtifact.instructionPC 2870 = 3603 := by rfl
@[simp] theorem pc2857 : Artifact.submissionArtifact.instructionPC 2871 = 3604 := by rfl
@[simp] theorem pc2858 : Artifact.submissionArtifact.instructionPC 2872 = 3606 := by rfl
@[simp] theorem pc2859 : Artifact.submissionArtifact.instructionPC 2873 = 3607 := by rfl
@[simp] theorem pc2860 : Artifact.submissionArtifact.instructionPC 2874 = 3608 := by rfl
@[simp] theorem pc2861 : Artifact.submissionArtifact.instructionPC 2875 = 3609 := by rfl
@[simp] theorem pc2862 : Artifact.submissionArtifact.instructionPC 2876 = 3610 := by rfl
@[simp] theorem pc2863 : Artifact.submissionArtifact.instructionPC 2877 = 3611 := by rfl
@[simp] theorem pc2864 : Artifact.submissionArtifact.instructionPC 2878 = 3612 := by rfl
@[simp] theorem pc2865 : Artifact.submissionArtifact.instructionPC 2879 = 3613 := by rfl
@[simp] theorem pc2866 : Artifact.submissionArtifact.instructionPC 2880 = 3614 := by rfl
@[simp] theorem pc2867 : Artifact.submissionArtifact.instructionPC 2881 = 3615 := by rfl
@[simp] theorem pc2868 : Artifact.submissionArtifact.instructionPC 2882 = 3616 := by rfl
@[simp] theorem pc2869 : Artifact.submissionArtifact.instructionPC 2883 = 3618 := by rfl
@[simp] theorem pc2870 : Artifact.submissionArtifact.instructionPC 2884 = 3619 := by rfl
@[simp] theorem pc2871 : Artifact.submissionArtifact.instructionPC 2885 = 3620 := by rfl
@[simp] theorem pc2872 : Artifact.submissionArtifact.instructionPC 2886 = 3621 := by rfl
@[simp] theorem pc2873 : Artifact.submissionArtifact.instructionPC 2887 = 3622 := by rfl
@[simp] theorem pc2874 : Artifact.submissionArtifact.instructionPC 2888 = 3624 := by rfl
@[simp] theorem pc2875 : Artifact.submissionArtifact.instructionPC 2889 = 3625 := by rfl
@[simp] theorem pc2876 : Artifact.submissionArtifact.instructionPC 2890 = 3626 := by rfl
@[simp] theorem pc2877 : Artifact.submissionArtifact.instructionPC 2891 = 3627 := by rfl
@[simp] theorem pc2878 : Artifact.submissionArtifact.instructionPC 2892 = 3628 := by rfl
@[simp] theorem pc2879 : Artifact.submissionArtifact.instructionPC 2893 = 3629 := by rfl
@[simp] theorem pc2880 : Artifact.submissionArtifact.instructionPC 2894 = 3630 := by rfl
@[simp] theorem pc2881 : Artifact.submissionArtifact.instructionPC 2895 = 3631 := by rfl
@[simp] theorem pc2882 : Artifact.submissionArtifact.instructionPC 2896 = 3632 := by rfl
@[simp] theorem pc2883 : Artifact.submissionArtifact.instructionPC 2897 = 3634 := by rfl
@[simp] theorem pc2884 : Artifact.submissionArtifact.instructionPC 2898 = 3635 := by rfl
@[simp] theorem pc2885 : Artifact.submissionArtifact.instructionPC 2899 = 3636 := by rfl
@[simp] theorem pc2886 : Artifact.submissionArtifact.instructionPC 2900 = 3637 := by rfl
@[simp] theorem pc2887 : Artifact.submissionArtifact.instructionPC 2901 = 3638 := by rfl
@[simp] theorem pc2888 : Artifact.submissionArtifact.instructionPC 2902 = 3639 := by rfl
@[simp] theorem pc2889 : Artifact.submissionArtifact.instructionPC 2903 = 3640 := by rfl
@[simp] theorem pc2890 : Artifact.submissionArtifact.instructionPC 2904 = 3641 := by rfl
@[simp] theorem pc2891 : Artifact.submissionArtifact.instructionPC 2905 = 3642 := by rfl
@[simp] theorem pc2892 : Artifact.submissionArtifact.instructionPC 2906 = 3643 := by rfl
@[simp] theorem pc2893 : Artifact.submissionArtifact.instructionPC 2907 = 3644 := by rfl
@[simp] theorem pc2894 : Artifact.submissionArtifact.instructionPC 2908 = 3645 := by rfl
@[simp] theorem pc2895 : Artifact.submissionArtifact.instructionPC 2909 = 3646 := by rfl
@[simp] theorem pc2896 : Artifact.submissionArtifact.instructionPC 2910 = 3647 := by rfl
@[simp] theorem pc2897 : Artifact.submissionArtifact.instructionPC 2911 = 3648 := by rfl
@[simp] theorem pc2898 : Artifact.submissionArtifact.instructionPC 2912 = 3649 := by rfl
@[simp] theorem pc2899 : Artifact.submissionArtifact.instructionPC 2913 = 3650 := by rfl
@[simp] theorem pc2900 : Artifact.submissionArtifact.instructionPC 2914 = 3651 := by rfl
@[simp] theorem pc2901 : Artifact.submissionArtifact.instructionPC 2915 = 3652 := by rfl
@[simp] theorem pc2902 : Artifact.submissionArtifact.instructionPC 2916 = 3655 := by rfl
@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2917 = 3656 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2918 = 3659 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2919 = 3660 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2920 = 3661 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2921 = 3662 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2922 = 3663 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths
