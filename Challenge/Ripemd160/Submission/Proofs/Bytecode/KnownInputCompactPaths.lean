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
  [opAt 2837 .JUMPDEST,
   opAt 2838 .CALLDATASIZE,
   pushAt 2839 2 1000,
   opAt 2840 .EQ,
   pushAt 2841 2 4828,
   opAt 2842 .JUMPI]

def sizeFallbackPath : List Located :=
  [pushAt 2843 2 4766,
   opAt 2844 .JUMP]

def checkEntryPath : List Located :=
  [opAt 2845 .JUMPDEST,
   pushAt 2846 0 0,
   opAt 2847 .CALLDATALOAD,
   opAt 2848 (.Dup ⟨0, by decide⟩),
   pushAt 2849 8 7016996765293437281,
   opAt 2850 (.Dup ⟨0, by decide⟩),
   pushAt 2851 1 64,
   opAt 2852 .SHL,
   opAt 2853 .OR,
   opAt 2854 (.Dup ⟨0, by decide⟩),
   pushAt 2855 1 128,
   opAt 2856 .SHL,
   opAt 2857 .OR,
   opAt 2858 .XOR,
   pushAt 2859 1 32]

def loopPath : List Located :=
  [opAt 2860 .JUMPDEST,
   opAt 2861 (.Dup ⟨0, by decide⟩),
   opAt 2862 .CALLDATALOAD,
   opAt 2863 (.Dup ⟨3, by decide⟩),
   opAt 2864 .XOR,
   opAt 2865 (.Swap ⟨0, by decide⟩),
   opAt 2866 (.Swap ⟨1, by decide⟩),
   opAt 2867 .OR,
   opAt 2868 (.Swap ⟨0, by decide⟩),
   pushAt 2869 1 32,
   opAt 2870 .ADD,
   pushAt 2871 2 992,
   opAt 2872 (.Dup ⟨1, by decide⟩),
   opAt 2873 .LT,
   pushAt 2874 2 4854,
   opAt 2875 .JUMPI]

def tailPath : List Located :=
  [opAt 2876 .POP,
   pushAt 2877 2 992,
   opAt 2878 .CALLDATALOAD,
   pushAt 2879 1 192,
   opAt 2880 .SHR,
   opAt 2881 (.Dup ⟨2, by decide⟩),
   pushAt 2882 1 192,
   opAt 2883 .SHR,
   opAt 2884 .XOR,
   opAt 2885 .OR,
   opAt 2886 (.Swap ⟨0, by decide⟩),
   opAt 2887 .POP,
   pushAt 2888 2 4766,
   opAt 2889 .JUMPI]

def bodyPath : List Located :=
  [opAt 2890 (.Dup ⟨2, by decide⟩),
   pushAt 2891 1 6,
   opAt 2892 .SHR,
   pushAt 2893 1 21,
   opAt 2894 .MUL,
   pushAt 2895 2 4958,
   opAt 2896 .ADD,
   pushAt 2897 1 20,
   opAt 2898 (.Swap ⟨0, by decide⟩),
   pushAt 2899 0 0,
   opAt 2900 .CODECOPY,
   pushAt 2901 0 0,
   opAt 2902 .MLOAD,
   pushAt 2903 1 224,
   opAt 2904 .SHR,
   pushAt 2905 1 32,
   opAt 2906 .MSTORE,
   pushAt 2907 1 4,
   opAt 2908 .MLOAD,
   pushAt 2909 1 224,
   opAt 2910 .SHR,
   pushAt 2911 1 64,
   opAt 2912 .MSTORE,
   pushAt 2913 1 8,
   opAt 2914 .MLOAD,
   pushAt 2915 1 224,
   opAt 2916 .SHR,
   pushAt 2917 1 96,
   opAt 2918 .MSTORE,
   pushAt 2919 1 12,
   opAt 2920 .MLOAD,
   pushAt 2921 1 224,
   opAt 2922 .SHR,
   pushAt 2923 1 128,
   opAt 2924 .MSTORE,
   pushAt 2925 1 16,
   opAt 2926 .MLOAD,
   pushAt 2927 1 224,
   opAt 2928 .SHR,
   pushAt 2929 1 160,
   opAt 2930 .MSTORE,
   opAt 2931 .POP,
   opAt 2932 .JUMP]

@[simp] theorem pc2813 : Artifact.submissionArtifact.instructionPC 2833 = 3529 := by rfl
@[simp] theorem pc2814 : Artifact.submissionArtifact.instructionPC 2834 = 3531 := by rfl
@[simp] theorem pc2815 : Artifact.submissionArtifact.instructionPC 2835 = 3532 := by rfl
@[simp] theorem pc2816 : Artifact.submissionArtifact.instructionPC 2836 = 3533 := by rfl
@[simp] theorem pc2817 : Artifact.submissionArtifact.instructionPC 2837 = 3534 := by rfl
@[simp] theorem pc2818 : Artifact.submissionArtifact.instructionPC 2838 = 3535 := by rfl
@[simp] theorem pc2819 : Artifact.submissionArtifact.instructionPC 2839 = 3536 := by rfl
@[simp] theorem pc2820 : Artifact.submissionArtifact.instructionPC 2840 = 3537 := by rfl
@[simp] theorem pc2821 : Artifact.submissionArtifact.instructionPC 2841 = 3538 := by rfl
@[simp] theorem pc2822 : Artifact.submissionArtifact.instructionPC 2842 = 3539 := by rfl
@[simp] theorem pc2823 : Artifact.submissionArtifact.instructionPC 2843 = 3540 := by rfl
@[simp] theorem pc2824 : Artifact.submissionArtifact.instructionPC 2844 = 3541 := by rfl
@[simp] theorem pc2825 : Artifact.submissionArtifact.instructionPC 2845 = 3542 := by rfl
@[simp] theorem pc2826 : Artifact.submissionArtifact.instructionPC 2846 = 3543 := by rfl
@[simp] theorem pc2827 : Artifact.submissionArtifact.instructionPC 2847 = 3544 := by rfl
@[simp] theorem pc2828 : Artifact.submissionArtifact.instructionPC 2848 = 3545 := by rfl
@[simp] theorem pc2829 : Artifact.submissionArtifact.instructionPC 2849 = 3546 := by rfl
@[simp] theorem pc2830 : Artifact.submissionArtifact.instructionPC 2850 = 3547 := by rfl
@[simp] theorem pc2831 : Artifact.submissionArtifact.instructionPC 2851 = 3548 := by rfl
@[simp] theorem pc2832 : Artifact.submissionArtifact.instructionPC 2852 = 3549 := by rfl
@[simp] theorem pc2833 : Artifact.submissionArtifact.instructionPC 2853 = 3551 := by rfl
@[simp] theorem pc2834 : Artifact.submissionArtifact.instructionPC 2854 = 3552 := by rfl
@[simp] theorem pc2835 : Artifact.submissionArtifact.instructionPC 2855 = 3555 := by rfl
@[simp] theorem pc2836 : Artifact.submissionArtifact.instructionPC 2856 = 3556 := by rfl
@[simp] theorem pc2837 : Artifact.submissionArtifact.instructionPC 2857 = 3557 := by rfl
@[simp] theorem pc2838 : Artifact.submissionArtifact.instructionPC 2858 = 3558 := by rfl
@[simp] theorem pc2839 : Artifact.submissionArtifact.instructionPC 2859 = 3559 := by rfl
@[simp] theorem pc2840 : Artifact.submissionArtifact.instructionPC 2860 = 3560 := by rfl
@[simp] theorem pc2841 : Artifact.submissionArtifact.instructionPC 2861 = 3561 := by rfl
@[simp] theorem pc2842 : Artifact.submissionArtifact.instructionPC 2862 = 3562 := by rfl
@[simp] theorem pc2843 : Artifact.submissionArtifact.instructionPC 2863 = 3563 := by rfl
@[simp] theorem pc2844 : Artifact.submissionArtifact.instructionPC 2864 = 3564 := by rfl
@[simp] theorem pc2845 : Artifact.submissionArtifact.instructionPC 2865 = 3566 := by rfl
@[simp] theorem pc2846 : Artifact.submissionArtifact.instructionPC 2866 = 3567 := by rfl
@[simp] theorem pc2847 : Artifact.submissionArtifact.instructionPC 2867 = 3568 := by rfl
@[simp] theorem pc2848 : Artifact.submissionArtifact.instructionPC 2868 = 3569 := by rfl
@[simp] theorem pc2849 : Artifact.submissionArtifact.instructionPC 2869 = 3570 := by rfl
@[simp] theorem pc2850 : Artifact.submissionArtifact.instructionPC 2870 = 3571 := by rfl
@[simp] theorem pc2851 : Artifact.submissionArtifact.instructionPC 2871 = 3572 := by rfl
@[simp] theorem pc2852 : Artifact.submissionArtifact.instructionPC 2872 = 3573 := by rfl
@[simp] theorem pc2853 : Artifact.submissionArtifact.instructionPC 2873 = 3574 := by rfl
@[simp] theorem pc2854 : Artifact.submissionArtifact.instructionPC 2874 = 3576 := by rfl
@[simp] theorem pc2855 : Artifact.submissionArtifact.instructionPC 2875 = 3577 := by rfl
@[simp] theorem pc2856 : Artifact.submissionArtifact.instructionPC 2876 = 3578 := by rfl
@[simp] theorem pc2857 : Artifact.submissionArtifact.instructionPC 2877 = 3579 := by rfl
@[simp] theorem pc2858 : Artifact.submissionArtifact.instructionPC 2878 = 3580 := by rfl
@[simp] theorem pc2859 : Artifact.submissionArtifact.instructionPC 2879 = 3581 := by rfl
@[simp] theorem pc2860 : Artifact.submissionArtifact.instructionPC 2880 = 3582 := by rfl
@[simp] theorem pc2861 : Artifact.submissionArtifact.instructionPC 2881 = 3583 := by rfl
@[simp] theorem pc2862 : Artifact.submissionArtifact.instructionPC 2882 = 3584 := by rfl
@[simp] theorem pc2863 : Artifact.submissionArtifact.instructionPC 2883 = 3585 := by rfl
@[simp] theorem pc2864 : Artifact.submissionArtifact.instructionPC 2884 = 3586 := by rfl
@[simp] theorem pc2865 : Artifact.submissionArtifact.instructionPC 2885 = 3587 := by rfl
@[simp] theorem pc2866 : Artifact.submissionArtifact.instructionPC 2886 = 3588 := by rfl
@[simp] theorem pc2867 : Artifact.submissionArtifact.instructionPC 2887 = 3589 := by rfl
@[simp] theorem pc2868 : Artifact.submissionArtifact.instructionPC 2888 = 3590 := by rfl
@[simp] theorem pc2869 : Artifact.submissionArtifact.instructionPC 2889 = 3591 := by rfl
@[simp] theorem pc2870 : Artifact.submissionArtifact.instructionPC 2890 = 3592 := by rfl
@[simp] theorem pc2871 : Artifact.submissionArtifact.instructionPC 2891 = 3593 := by rfl
@[simp] theorem pc2872 : Artifact.submissionArtifact.instructionPC 2892 = 3594 := by rfl
@[simp] theorem pc2873 : Artifact.submissionArtifact.instructionPC 2893 = 3597 := by rfl
@[simp] theorem pc2874 : Artifact.submissionArtifact.instructionPC 2894 = 3598 := by rfl
@[simp] theorem pc2875 : Artifact.submissionArtifact.instructionPC 2895 = 3601 := by rfl
@[simp] theorem pc2876 : Artifact.submissionArtifact.instructionPC 2896 = 3602 := by rfl
@[simp] theorem pc2877 : Artifact.submissionArtifact.instructionPC 2897 = 3603 := by rfl
@[simp] theorem pc2878 : Artifact.submissionArtifact.instructionPC 2898 = 3604 := by rfl
@[simp] theorem pc2879 : Artifact.submissionArtifact.instructionPC 2899 = 3605 := by rfl
@[simp] theorem pc2880 : Artifact.submissionArtifact.instructionPC 2900 = 3606 := by rfl
@[simp] theorem pc2881 : Artifact.submissionArtifact.instructionPC 2901 = 3607 := by rfl
@[simp] theorem pc2882 : Artifact.submissionArtifact.instructionPC 2902 = 3608 := by rfl
@[simp] theorem pc2883 : Artifact.submissionArtifact.instructionPC 2903 = 3609 := by rfl
@[simp] theorem pc2884 : Artifact.submissionArtifact.instructionPC 2904 = 3610 := by rfl
@[simp] theorem pc2885 : Artifact.submissionArtifact.instructionPC 2905 = 3612 := by rfl
@[simp] theorem pc2886 : Artifact.submissionArtifact.instructionPC 2906 = 3613 := by rfl
@[simp] theorem pc2887 : Artifact.submissionArtifact.instructionPC 2907 = 3614 := by rfl
@[simp] theorem pc2888 : Artifact.submissionArtifact.instructionPC 2908 = 3616 := by rfl
@[simp] theorem pc2889 : Artifact.submissionArtifact.instructionPC 2909 = 3617 := by rfl
@[simp] theorem pc2890 : Artifact.submissionArtifact.instructionPC 2910 = 3618 := by rfl
@[simp] theorem pc2891 : Artifact.submissionArtifact.instructionPC 2911 = 3619 := by rfl
@[simp] theorem pc2892 : Artifact.submissionArtifact.instructionPC 2912 = 3620 := by rfl
@[simp] theorem pc2893 : Artifact.submissionArtifact.instructionPC 2913 = 3621 := by rfl
@[simp] theorem pc2894 : Artifact.submissionArtifact.instructionPC 2914 = 3622 := by rfl
@[simp] theorem pc2895 : Artifact.submissionArtifact.instructionPC 2915 = 3623 := by rfl
@[simp] theorem pc2896 : Artifact.submissionArtifact.instructionPC 2916 = 3624 := by rfl
@[simp] theorem pc2897 : Artifact.submissionArtifact.instructionPC 2917 = 3625 := by rfl
@[simp] theorem pc2898 : Artifact.submissionArtifact.instructionPC 2918 = 3626 := by rfl
@[simp] theorem pc2899 : Artifact.submissionArtifact.instructionPC 2919 = 3627 := by rfl
@[simp] theorem pc2900 : Artifact.submissionArtifact.instructionPC 2920 = 3628 := by rfl
@[simp] theorem pc2901 : Artifact.submissionArtifact.instructionPC 2921 = 3629 := by rfl
@[simp] theorem pc2902 : Artifact.submissionArtifact.instructionPC 2922 = 3631 := by rfl
@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2923 = 3632 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2924 = 3633 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2925 = 3634 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2926 = 3635 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2927 = 3636 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2928 = 3637 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths
