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
  [opAt 2813 .JUMPDEST,
   opAt 2814 .CALLDATASIZE,
   pushAt 2815 2 1000,
   opAt 2816 .EQ,
   pushAt 2817 2 4828,
   opAt 2818 .JUMPI]

def sizeFallbackPath : List Located :=
  [pushAt 2819 2 4766,
   opAt 2820 .JUMP]

def checkEntryPath : List Located :=
  [opAt 2821 .JUMPDEST,
   pushAt 2822 0 0,
   opAt 2823 .CALLDATALOAD,
   opAt 2824 (.Dup ⟨0, by decide⟩),
   pushAt 2825 8 7016996765293437281,
   opAt 2826 (.Dup ⟨0, by decide⟩),
   pushAt 2827 1 64,
   opAt 2828 .SHL,
   opAt 2829 .OR,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   pushAt 2831 1 128,
   opAt 2832 .SHL,
   opAt 2833 .OR,
   opAt 2834 .XOR,
   pushAt 2835 1 32]

def loopPath : List Located :=
  [opAt 2836 .JUMPDEST,
   opAt 2837 (.Dup ⟨0, by decide⟩),
   opAt 2838 .CALLDATALOAD,
   opAt 2839 (.Dup ⟨3, by decide⟩),
   opAt 2840 .XOR,
   opAt 2841 (.Swap ⟨0, by decide⟩),
   opAt 2842 (.Swap ⟨1, by decide⟩),
   opAt 2843 .OR,
   opAt 2844 (.Swap ⟨0, by decide⟩),
   pushAt 2845 1 32,
   opAt 2846 .ADD,
   pushAt 2847 2 992,
   opAt 2848 (.Dup ⟨1, by decide⟩),
   opAt 2849 .LT,
   pushAt 2850 2 4854,
   opAt 2851 .JUMPI]

def tailPath : List Located :=
  [opAt 2852 .POP,
   pushAt 2853 2 992,
   opAt 2854 .CALLDATALOAD,
   pushAt 2855 1 192,
   opAt 2856 .SHR,
   opAt 2857 (.Dup ⟨2, by decide⟩),
   pushAt 2858 1 192,
   opAt 2859 .SHR,
   opAt 2860 .XOR,
   opAt 2861 .OR,
   opAt 2862 (.Swap ⟨0, by decide⟩),
   opAt 2863 .POP,
   pushAt 2864 2 4766,
   opAt 2865 .JUMPI]

def bodyPath : List Located :=
  [opAt 2866 (.Dup ⟨2, by decide⟩),
   pushAt 2867 1 6,
   opAt 2868 .SHR,
   pushAt 2869 1 21,
   opAt 2870 .MUL,
   pushAt 2871 2 4958,
   opAt 2872 .ADD,
   pushAt 2873 1 20,
   opAt 2874 (.Swap ⟨0, by decide⟩),
   pushAt 2875 0 0,
   opAt 2876 .CODECOPY,
   pushAt 2877 0 0,
   opAt 2878 .MLOAD,
   pushAt 2879 1 224,
   opAt 2880 .SHR,
   pushAt 2881 1 32,
   opAt 2882 .MSTORE,
   pushAt 2883 1 4,
   opAt 2884 .MLOAD,
   pushAt 2885 1 224,
   opAt 2886 .SHR,
   pushAt 2887 1 64,
   opAt 2888 .MSTORE,
   pushAt 2889 1 8,
   opAt 2890 .MLOAD,
   pushAt 2891 1 224,
   opAt 2892 .SHR,
   pushAt 2893 1 96,
   opAt 2894 .MSTORE,
   pushAt 2895 1 12,
   opAt 2896 .MLOAD,
   pushAt 2897 1 224,
   opAt 2898 .SHR,
   pushAt 2899 1 128,
   opAt 2900 .MSTORE,
   pushAt 2901 1 16,
   opAt 2902 .MLOAD,
   pushAt 2903 1 224,
   opAt 2904 .SHR,
   pushAt 2905 1 160,
   opAt 2906 .MSTORE,
   opAt 2907 .POP,
   opAt 2908 .JUMP]

@[simp] theorem pc2813 : Artifact.submissionArtifact.instructionPC 2831 = 3563 := by rfl
@[simp] theorem pc2814 : Artifact.submissionArtifact.instructionPC 2832 = 3564 := by rfl
@[simp] theorem pc2815 : Artifact.submissionArtifact.instructionPC 2833 = 3565 := by rfl
@[simp] theorem pc2816 : Artifact.submissionArtifact.instructionPC 2834 = 3567 := by rfl
@[simp] theorem pc2817 : Artifact.submissionArtifact.instructionPC 2835 = 3568 := by rfl
@[simp] theorem pc2818 : Artifact.submissionArtifact.instructionPC 2836 = 3569 := by rfl
@[simp] theorem pc2819 : Artifact.submissionArtifact.instructionPC 2837 = 3570 := by rfl
@[simp] theorem pc2820 : Artifact.submissionArtifact.instructionPC 2838 = 3571 := by rfl
@[simp] theorem pc2821 : Artifact.submissionArtifact.instructionPC 2839 = 3573 := by rfl
@[simp] theorem pc2822 : Artifact.submissionArtifact.instructionPC 2840 = 3574 := by rfl
@[simp] theorem pc2823 : Artifact.submissionArtifact.instructionPC 2841 = 3575 := by rfl
@[simp] theorem pc2824 : Artifact.submissionArtifact.instructionPC 2842 = 3576 := by rfl
@[simp] theorem pc2825 : Artifact.submissionArtifact.instructionPC 2843 = 3577 := by rfl
@[simp] theorem pc2826 : Artifact.submissionArtifact.instructionPC 2844 = 3578 := by rfl
@[simp] theorem pc2827 : Artifact.submissionArtifact.instructionPC 2845 = 3579 := by rfl
@[simp] theorem pc2828 : Artifact.submissionArtifact.instructionPC 2846 = 3580 := by rfl
@[simp] theorem pc2829 : Artifact.submissionArtifact.instructionPC 2847 = 3581 := by rfl
@[simp] theorem pc2830 : Artifact.submissionArtifact.instructionPC 2848 = 3583 := by rfl
@[simp] theorem pc2831 : Artifact.submissionArtifact.instructionPC 2849 = 3584 := by rfl
@[simp] theorem pc2832 : Artifact.submissionArtifact.instructionPC 2850 = 3585 := by rfl
@[simp] theorem pc2833 : Artifact.submissionArtifact.instructionPC 2851 = 3586 := by rfl
@[simp] theorem pc2834 : Artifact.submissionArtifact.instructionPC 2852 = 3587 := by rfl
@[simp] theorem pc2835 : Artifact.submissionArtifact.instructionPC 2853 = 3588 := by rfl
@[simp] theorem pc2836 : Artifact.submissionArtifact.instructionPC 2854 = 3589 := by rfl
@[simp] theorem pc2837 : Artifact.submissionArtifact.instructionPC 2855 = 3590 := by rfl
@[simp] theorem pc2838 : Artifact.submissionArtifact.instructionPC 2856 = 3591 := by rfl
@[simp] theorem pc2839 : Artifact.submissionArtifact.instructionPC 2857 = 3592 := by rfl
@[simp] theorem pc2840 : Artifact.submissionArtifact.instructionPC 2858 = 3593 := by rfl
@[simp] theorem pc2841 : Artifact.submissionArtifact.instructionPC 2859 = 3594 := by rfl
@[simp] theorem pc2842 : Artifact.submissionArtifact.instructionPC 2860 = 3595 := by rfl
@[simp] theorem pc2843 : Artifact.submissionArtifact.instructionPC 2861 = 3596 := by rfl
@[simp] theorem pc2844 : Artifact.submissionArtifact.instructionPC 2862 = 3597 := by rfl
@[simp] theorem pc2845 : Artifact.submissionArtifact.instructionPC 2863 = 3598 := by rfl
@[simp] theorem pc2846 : Artifact.submissionArtifact.instructionPC 2864 = 3599 := by rfl
@[simp] theorem pc2847 : Artifact.submissionArtifact.instructionPC 2865 = 3600 := by rfl
@[simp] theorem pc2848 : Artifact.submissionArtifact.instructionPC 2866 = 3601 := by rfl
@[simp] theorem pc2849 : Artifact.submissionArtifact.instructionPC 2867 = 3604 := by rfl
@[simp] theorem pc2850 : Artifact.submissionArtifact.instructionPC 2868 = 3605 := by rfl
@[simp] theorem pc2851 : Artifact.submissionArtifact.instructionPC 2869 = 3607 := by rfl
@[simp] theorem pc2852 : Artifact.submissionArtifact.instructionPC 2870 = 3608 := by rfl
@[simp] theorem pc2853 : Artifact.submissionArtifact.instructionPC 2871 = 3609 := by rfl
@[simp] theorem pc2854 : Artifact.submissionArtifact.instructionPC 2872 = 3610 := by rfl
@[simp] theorem pc2855 : Artifact.submissionArtifact.instructionPC 2873 = 3611 := by rfl
@[simp] theorem pc2856 : Artifact.submissionArtifact.instructionPC 2874 = 3612 := by rfl
@[simp] theorem pc2857 : Artifact.submissionArtifact.instructionPC 2875 = 3613 := by rfl
@[simp] theorem pc2858 : Artifact.submissionArtifact.instructionPC 2876 = 3614 := by rfl
@[simp] theorem pc2859 : Artifact.submissionArtifact.instructionPC 2877 = 3615 := by rfl
@[simp] theorem pc2860 : Artifact.submissionArtifact.instructionPC 2878 = 3616 := by rfl
@[simp] theorem pc2861 : Artifact.submissionArtifact.instructionPC 2879 = 3617 := by rfl
@[simp] theorem pc2862 : Artifact.submissionArtifact.instructionPC 2880 = 3619 := by rfl
@[simp] theorem pc2863 : Artifact.submissionArtifact.instructionPC 2881 = 3620 := by rfl
@[simp] theorem pc2864 : Artifact.submissionArtifact.instructionPC 2882 = 3621 := by rfl
@[simp] theorem pc2865 : Artifact.submissionArtifact.instructionPC 2883 = 3622 := by rfl
@[simp] theorem pc2866 : Artifact.submissionArtifact.instructionPC 2884 = 3623 := by rfl
@[simp] theorem pc2867 : Artifact.submissionArtifact.instructionPC 2885 = 3625 := by rfl
@[simp] theorem pc2868 : Artifact.submissionArtifact.instructionPC 2886 = 3626 := by rfl
@[simp] theorem pc2869 : Artifact.submissionArtifact.instructionPC 2887 = 3627 := by rfl
@[simp] theorem pc2870 : Artifact.submissionArtifact.instructionPC 2888 = 3628 := by rfl
@[simp] theorem pc2871 : Artifact.submissionArtifact.instructionPC 2889 = 3629 := by rfl
@[simp] theorem pc2872 : Artifact.submissionArtifact.instructionPC 2890 = 3630 := by rfl
@[simp] theorem pc2873 : Artifact.submissionArtifact.instructionPC 2891 = 3631 := by rfl
@[simp] theorem pc2874 : Artifact.submissionArtifact.instructionPC 2892 = 3632 := by rfl
@[simp] theorem pc2875 : Artifact.submissionArtifact.instructionPC 2893 = 3633 := by rfl
@[simp] theorem pc2876 : Artifact.submissionArtifact.instructionPC 2894 = 3635 := by rfl
@[simp] theorem pc2877 : Artifact.submissionArtifact.instructionPC 2895 = 3636 := by rfl
@[simp] theorem pc2878 : Artifact.submissionArtifact.instructionPC 2896 = 3637 := by rfl
@[simp] theorem pc2879 : Artifact.submissionArtifact.instructionPC 2897 = 3638 := by rfl
@[simp] theorem pc2880 : Artifact.submissionArtifact.instructionPC 2898 = 3639 := by rfl
@[simp] theorem pc2881 : Artifact.submissionArtifact.instructionPC 2899 = 3640 := by rfl
@[simp] theorem pc2882 : Artifact.submissionArtifact.instructionPC 2900 = 3641 := by rfl
@[simp] theorem pc2883 : Artifact.submissionArtifact.instructionPC 2901 = 3642 := by rfl
@[simp] theorem pc2884 : Artifact.submissionArtifact.instructionPC 2902 = 3643 := by rfl
@[simp] theorem pc2885 : Artifact.submissionArtifact.instructionPC 2903 = 3644 := by rfl
@[simp] theorem pc2886 : Artifact.submissionArtifact.instructionPC 2904 = 3645 := by rfl
@[simp] theorem pc2887 : Artifact.submissionArtifact.instructionPC 2905 = 3646 := by rfl
@[simp] theorem pc2888 : Artifact.submissionArtifact.instructionPC 2906 = 3647 := by rfl
@[simp] theorem pc2889 : Artifact.submissionArtifact.instructionPC 2907 = 3648 := by rfl
@[simp] theorem pc2890 : Artifact.submissionArtifact.instructionPC 2908 = 3649 := by rfl
@[simp] theorem pc2891 : Artifact.submissionArtifact.instructionPC 2909 = 3650 := by rfl
@[simp] theorem pc2892 : Artifact.submissionArtifact.instructionPC 2910 = 3651 := by rfl
@[simp] theorem pc2893 : Artifact.submissionArtifact.instructionPC 2911 = 3652 := by rfl
@[simp] theorem pc2894 : Artifact.submissionArtifact.instructionPC 2912 = 3653 := by rfl
@[simp] theorem pc2895 : Artifact.submissionArtifact.instructionPC 2913 = 3656 := by rfl
@[simp] theorem pc2896 : Artifact.submissionArtifact.instructionPC 2914 = 3657 := by rfl
@[simp] theorem pc2897 : Artifact.submissionArtifact.instructionPC 2915 = 3660 := by rfl
@[simp] theorem pc2898 : Artifact.submissionArtifact.instructionPC 2916 = 3661 := by rfl
@[simp] theorem pc2899 : Artifact.submissionArtifact.instructionPC 2917 = 3662 := by rfl
@[simp] theorem pc2900 : Artifact.submissionArtifact.instructionPC 2918 = 3663 := by rfl
@[simp] theorem pc2901 : Artifact.submissionArtifact.instructionPC 2919 = 3664 := by rfl
@[simp] theorem pc2902 : Artifact.submissionArtifact.instructionPC 2920 = 3665 := by rfl
@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2921 = 3666 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2922 = 3667 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2923 = 3668 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2924 = 3669 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2925 = 3670 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2926 = 3672 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths
