import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace Challenge.Modexp.Submission.Proofs.Fast
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

def csGenericPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3748 .JUMPDEST,
   pushAt 3749 2 9344,
   opAt 3750 .MLOAD,
   pushAt 3751 2 256,
   opAt 3752 .EQ,
   pushAt 3753 2 5030,
   opAt 3754 .JUMPI,
   pushAt 3755 2 9344,
   opAt 3756 .MLOAD,
   pushAt 3757 1 128,
   opAt 3758 .EQ,
   pushAt 3759 2 3881,
   opAt 3760 .JUMPI,
   pushAt 3761 2 9440,
   opAt 3762 .MLOAD,
   pushAt 3763 2 9408,
   opAt 3764 .MLOAD,
   opAt 3765 (.Dup ⟨0, by decide⟩),
   pushAt 3766 2 7168,
   opAt 3767 .ADD,
   pushAt 3768 2 8256,
   opAt 3769 .POP,
   opAt 3770 (.Swap ⟨0, by decide⟩),
   pushAt 3771 0 0,
   opAt 3772 (.Swap ⟨2, by decide⟩),
   pushAt 3773 2 2144,
   opAt 3774 .JUMP]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3748 .JUMPDEST,
   pushAt 3749 2 9344,
   opAt 3750 .MLOAD,
   pushAt 3751 2 256,
   opAt 3752 .EQ,
   pushAt 3753 2 5030,
   opAt 3754 .JUMPI,
   opAt 3775 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3748 .JUMPDEST,
   pushAt 3749 2 9344,
   opAt 3750 .MLOAD,
   pushAt 3751 2 256,
   opAt 3752 .EQ,
   pushAt 3753 2 5030,
   opAt 3754 .JUMPI,
   pushAt 3755 2 9344,
   opAt 3756 .MLOAD,
   pushAt 3757 1 128,
   opAt 3758 .EQ,
   pushAt 3759 2 3881,
   opAt 3760 .JUMPI,
   opAt 2932 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3776 2 8480,
   opAt 3777 .MLOAD,
   pushAt 3778 1 224,
   opAt 3779 .MLOAD,
   opAt 3780 (.Dup ⟨1, by decide⟩),
   opAt 3781 (.Dup ⟨1, by decide⟩),
   opAt 3782 .GT,
   opAt 3783 (.Swap ⟨1, by decide⟩),
   opAt 3784 .SUB,
   pushAt 3785 2 7392,
   opAt 3786 .MSTORE]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3787 2 8448,
   opAt 3788 .MLOAD,
   pushAt 3789 1 192,
   opAt 3790 .MLOAD,
   opAt 3791 (.Dup ⟨1, by decide⟩),
   opAt 3792 (.Dup ⟨1, by decide⟩),
   opAt 3793 .GT,
   opAt 3794 (.Swap ⟨1, by decide⟩),
   opAt 3795 .SUB,
   opAt 3796 (.Dup ⟨2, by decide⟩),
   opAt 3797 (.Dup ⟨1, by decide⟩),
   opAt 3798 .SUB,
   opAt 3799 (.Swap ⟨2, by decide⟩),
   opAt 3800 .GT,
   opAt 3801 .OR,
   opAt 3802 (.Swap ⟨0, by decide⟩),
   pushAt 3803 2 7360,
   opAt 3804 .MSTORE]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3805 2 8416,
   opAt 3806 .MLOAD,
   pushAt 3807 1 160,
   opAt 3808 .MLOAD,
   opAt 3809 (.Dup ⟨1, by decide⟩),
   opAt 3810 (.Dup ⟨1, by decide⟩),
   opAt 3811 .GT,
   opAt 3812 (.Swap ⟨1, by decide⟩),
   opAt 3813 .SUB,
   opAt 3814 (.Dup ⟨2, by decide⟩),
   opAt 3815 (.Dup ⟨1, by decide⟩),
   opAt 3816 .SUB,
   opAt 3817 (.Swap ⟨2, by decide⟩),
   opAt 3818 .GT,
   opAt 3819 .OR,
   opAt 3820 (.Swap ⟨0, by decide⟩),
   pushAt 3821 2 7328,
   opAt 3822 .MSTORE]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3823 2 8384,
   opAt 3824 .MLOAD,
   pushAt 3825 1 128,
   opAt 3826 .MLOAD,
   opAt 3827 (.Dup ⟨1, by decide⟩),
   opAt 3828 (.Dup ⟨1, by decide⟩),
   opAt 3829 .GT,
   opAt 3830 (.Swap ⟨1, by decide⟩),
   opAt 3831 .SUB,
   opAt 3832 (.Dup ⟨2, by decide⟩),
   opAt 3833 (.Dup ⟨1, by decide⟩),
   opAt 3834 .SUB,
   opAt 3835 (.Swap ⟨2, by decide⟩),
   opAt 3836 .GT,
   opAt 3837 .OR,
   opAt 3838 (.Swap ⟨0, by decide⟩),
   pushAt 3839 2 7296,
   opAt 3840 .MSTORE]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3841 .JUMPDEST,
   pushAt 3842 2 8352,
   opAt 3843 .MLOAD,
   pushAt 3844 1 96,
   opAt 3845 .MLOAD,
   opAt 3846 (.Dup ⟨1, by decide⟩),
   opAt 3847 (.Dup ⟨1, by decide⟩),
   opAt 3848 .GT,
   opAt 3849 (.Swap ⟨1, by decide⟩),
   opAt 3850 .SUB,
   opAt 3851 (.Dup ⟨2, by decide⟩),
   opAt 3852 (.Dup ⟨1, by decide⟩),
   opAt 3853 .SUB,
   opAt 3854 (.Swap ⟨2, by decide⟩),
   opAt 3855 .GT,
   opAt 3856 .OR,
   opAt 3857 (.Swap ⟨0, by decide⟩),
   pushAt 3858 2 7264,
   opAt 3859 .MSTORE]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3860 .JUMPDEST,
   pushAt 3861 2 8320,
   opAt 3862 .MLOAD,
   pushAt 3863 1 64,
   opAt 3864 .MLOAD,
   opAt 3865 (.Dup ⟨1, by decide⟩),
   opAt 3866 (.Dup ⟨1, by decide⟩),
   opAt 3867 .GT,
   opAt 3868 (.Swap ⟨1, by decide⟩),
   opAt 3869 .SUB,
   opAt 3870 (.Dup ⟨2, by decide⟩),
   opAt 3871 (.Dup ⟨1, by decide⟩),
   opAt 3872 .SUB,
   opAt 3873 (.Swap ⟨2, by decide⟩),
   opAt 3874 .GT,
   opAt 3875 .OR,
   opAt 3876 (.Swap ⟨0, by decide⟩),
   pushAt 3877 2 7232,
   opAt 3878 .MSTORE]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3879 2 8288,
   opAt 3880 .MLOAD,
   pushAt 3881 1 32,
   opAt 3882 .MLOAD,
   opAt 3883 (.Dup ⟨1, by decide⟩),
   opAt 3884 (.Dup ⟨1, by decide⟩),
   opAt 3885 .GT,
   opAt 3886 (.Swap ⟨1, by decide⟩),
   opAt 3887 .SUB,
   opAt 3888 (.Dup ⟨2, by decide⟩),
   opAt 3889 (.Dup ⟨1, by decide⟩),
   opAt 3890 .SUB,
   opAt 3891 (.Swap ⟨2, by decide⟩),
   opAt 3892 .GT,
   opAt 3893 .OR,
   opAt 3894 (.Swap ⟨0, by decide⟩),
   pushAt 3895 2 7200,
   opAt 3896 .MSTORE]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3897 2 8256,
   opAt 3898 .MLOAD,
   pushAt 3899 0 0,
   opAt 3900 .MLOAD,
   opAt 3901 (.Dup ⟨1, by decide⟩),
   opAt 3902 (.Dup ⟨1, by decide⟩),
   opAt 3903 .GT,
   opAt 3904 (.Swap ⟨1, by decide⟩),
   opAt 3905 .SUB,
   opAt 3906 (.Dup ⟨2, by decide⟩),
   opAt 3907 (.Dup ⟨1, by decide⟩),
   opAt 3908 .SUB,
   opAt 3909 (.Swap ⟨2, by decide⟩),
   opAt 3910 .GT,
   opAt 3911 .OR,
   opAt 3912 (.Swap ⟨0, by decide⟩),
   pushAt 3913 2 7168,
   opAt 3914 .MSTORE]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3915 .ISZERO,
   pushAt 3916 2 8224,
   opAt 3917 .MLOAD,
   opAt 3918 .OR,
   pushAt 3919 2 1087,
   opAt 3920 .NOT,
   pushAt 3921 2 5247,
   opAt 3922 .JUMP,
   opAt 3930 .JUMPDEST,
   opAt 3931 .MUL,
   pushAt 3932 2 8256,
   opAt 3933 .ADD,
   pushAt 3934 2 9344,
   opAt 3935 .MLOAD,
   opAt 3936 (.Swap ⟨1, by decide⟩),
   opAt 3937 .MCOPY,
   opAt 3938 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2933 2 8352,
   opAt 2934 .MLOAD,
   pushAt 2935 1 96,
   opAt 2936 .MLOAD,
   opAt 2937 (.Dup ⟨1, by decide⟩),
   opAt 2938 (.Dup ⟨1, by decide⟩),
   opAt 2939 .GT,
   opAt 2940 (.Swap ⟨1, by decide⟩),
   opAt 2941 .SUB,
   pushAt 2942 2 7264,
   opAt 2943 .MSTORE,
   pushAt 2944 2 5140,
   opAt 2945 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3860 .JUMPDEST,
   pushAt 3861 2 8320,
   opAt 3862 .MLOAD,
   pushAt 3863 1 64,
   opAt 3864 .MLOAD,
   opAt 3865 (.Dup ⟨1, by decide⟩),
   opAt 3866 (.Dup ⟨1, by decide⟩),
   opAt 3867 .GT,
   opAt 3868 (.Swap ⟨1, by decide⟩),
   opAt 3869 .SUB,
   opAt 3870 (.Dup ⟨2, by decide⟩),
   opAt 3871 (.Dup ⟨1, by decide⟩),
   opAt 3872 .SUB,
   opAt 3873 (.Swap ⟨2, by decide⟩),
   opAt 3874 .GT,
   opAt 3875 .OR,
   opAt 3876 (.Swap ⟨0, by decide⟩),
   pushAt 3877 2 7232,
   opAt 3878 .MSTORE]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3879 2 8288,
   opAt 3880 .MLOAD,
   pushAt 3881 1 32,
   opAt 3882 .MLOAD,
   opAt 3883 (.Dup ⟨1, by decide⟩),
   opAt 3884 (.Dup ⟨1, by decide⟩),
   opAt 3885 .GT,
   opAt 3886 (.Swap ⟨1, by decide⟩),
   opAt 3887 .SUB,
   opAt 3888 (.Dup ⟨2, by decide⟩),
   opAt 3889 (.Dup ⟨1, by decide⟩),
   opAt 3890 .SUB,
   opAt 3891 (.Swap ⟨2, by decide⟩),
   opAt 3892 .GT,
   opAt 3893 .OR,
   opAt 3894 (.Swap ⟨0, by decide⟩),
   pushAt 3895 2 7200,
   opAt 3896 .MSTORE]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3897 2 8256,
   opAt 3898 .MLOAD,
   pushAt 3899 0 0,
   opAt 3900 .MLOAD,
   opAt 3901 (.Dup ⟨1, by decide⟩),
   opAt 3902 (.Dup ⟨1, by decide⟩),
   opAt 3903 .GT,
   opAt 3904 (.Swap ⟨1, by decide⟩),
   opAt 3905 .SUB,
   opAt 3906 (.Dup ⟨2, by decide⟩),
   opAt 3907 (.Dup ⟨1, by decide⟩),
   opAt 3908 .SUB,
   opAt 3909 (.Swap ⟨2, by decide⟩),
   opAt 3910 .GT,
   opAt 3911 .OR,
   opAt 3912 (.Swap ⟨0, by decide⟩),
   pushAt 3913 2 7168,
   opAt 3914 .MSTORE]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3915 .ISZERO,
   pushAt 3916 2 8224,
   opAt 3917 .MLOAD,
   opAt 3918 .OR,
   pushAt 3919 2 1087,
   opAt 3920 .NOT,
   pushAt 3921 2 5247,
   opAt 3922 .JUMP,
   opAt 3930 .JUMPDEST,
   opAt 3931 .MUL,
   pushAt 3932 2 8256,
   opAt 3933 .ADD,
   pushAt 3934 2 9344,
   opAt 3935 .MLOAD,
   opAt 3936 (.Swap ⟨1, by decide⟩),
   opAt 3937 .MCOPY,
   opAt 3938 .JUMP]

@[simp] theorem fixedPC1617 : Artifact.submissionArtifact.instructionPC 1575 = 2139 := by rfl

@[simp] theorem fixedJump2220 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2139 = true := by
  simpa only [Artifact.instructionPC, fixedPC1617] using Artifact.isValidJumpDest_index 1575 (by rfl)

@[simp] theorem fixedPC1618 : Artifact.submissionArtifact.instructionPC 1576 = 2140 := by
  calc
    Artifact.submissionArtifact.instructionPC 1576 =
        Artifact.submissionArtifact.instructionPC 1575 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1575 _ (by rfl)
    _ = 2140 := by rw [fixedPC1617]; rfl

@[simp] theorem fixedPC1619 : Artifact.submissionArtifact.instructionPC 1577 = 2143 := by
  calc
    Artifact.submissionArtifact.instructionPC 1577 =
        Artifact.submissionArtifact.instructionPC 1576 + (YulEvmCompiler.Instr.push 2 3815).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1576 _ (by rfl)
    _ = 2143 := by rw [fixedPC1618]; rfl

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3748 = 4982 := by rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4982 = true := by
  simpa only [Artifact.instructionPC, fixedPC3777] using Artifact.isValidJumpDest_index 3748 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3749 = 4983 := by
  calc
    Artifact.submissionArtifact.instructionPC 3749 =
        Artifact.submissionArtifact.instructionPC 3748 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3748 _ (by rfl)
    _ = 4983 := by rw [fixedPC3777]; rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3750 = 4986 := by
  calc
    Artifact.submissionArtifact.instructionPC 3750 =
        Artifact.submissionArtifact.instructionPC 3749 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3749 _ (by rfl)
    _ = 4986 := by rw [fixedPC3778]; rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3751 = 4987 := by
  calc
    Artifact.submissionArtifact.instructionPC 3751 =
        Artifact.submissionArtifact.instructionPC 3750 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3750 _ (by rfl)
    _ = 4987 := by rw [fixedPC3779]; rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3752 = 4990 := by
  calc
    Artifact.submissionArtifact.instructionPC 3752 =
        Artifact.submissionArtifact.instructionPC 3751 + (YulEvmCompiler.Instr.push 2 256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3751 _ (by rfl)
    _ = 4990 := by rw [fixedPC3780]; rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3753 = 4991 := by
  calc
    Artifact.submissionArtifact.instructionPC 3753 =
        Artifact.submissionArtifact.instructionPC 3752 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3752 _ (by rfl)
    _ = 4991 := by rw [fixedPC3781]; rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3754 = 4994 := by
  calc
    Artifact.submissionArtifact.instructionPC 3754 =
        Artifact.submissionArtifact.instructionPC 3753 + (YulEvmCompiler.Instr.push 2 5030).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3753 _ (by rfl)
    _ = 4994 := by rw [fixedPC3782]; rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3755 = 4995 := by
  calc
    Artifact.submissionArtifact.instructionPC 3755 =
        Artifact.submissionArtifact.instructionPC 3754 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3754 _ (by rfl)
    _ = 4995 := by rw [fixedPC3783]; rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3756 = 4998 := by
  calc
    Artifact.submissionArtifact.instructionPC 3756 =
        Artifact.submissionArtifact.instructionPC 3755 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3755 _ (by rfl)
    _ = 4998 := by rw [fixedPC3784]; rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3757 = 4999 := by
  calc
    Artifact.submissionArtifact.instructionPC 3757 =
        Artifact.submissionArtifact.instructionPC 3756 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3756 _ (by rfl)
    _ = 4999 := by rw [fixedPC3785]; rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3758 = 5001 := by
  calc
    Artifact.submissionArtifact.instructionPC 3758 =
        Artifact.submissionArtifact.instructionPC 3757 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3757 _ (by rfl)
    _ = 5001 := by rw [fixedPC3786]; rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3759 = 5002 := by
  calc
    Artifact.submissionArtifact.instructionPC 3759 =
        Artifact.submissionArtifact.instructionPC 3758 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3758 _ (by rfl)
    _ = 5002 := by rw [fixedPC3787]; rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3760 = 5005 := by
  calc
    Artifact.submissionArtifact.instructionPC 3760 =
        Artifact.submissionArtifact.instructionPC 3759 + (YulEvmCompiler.Instr.push 2 3881).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3759 _ (by rfl)
    _ = 5005 := by rw [fixedPC3788]; rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3761 = 5006 := by
  calc
    Artifact.submissionArtifact.instructionPC 3761 =
        Artifact.submissionArtifact.instructionPC 3760 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3760 _ (by rfl)
    _ = 5006 := by rw [fixedPC3789]; rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3762 = 5009 := by
  calc
    Artifact.submissionArtifact.instructionPC 3762 =
        Artifact.submissionArtifact.instructionPC 3761 + (YulEvmCompiler.Instr.push 2 9440).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3761 _ (by rfl)
    _ = 5009 := by rw [fixedPC3790]; rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3763 = 5010 := by
  calc
    Artifact.submissionArtifact.instructionPC 3763 =
        Artifact.submissionArtifact.instructionPC 3762 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3762 _ (by rfl)
    _ = 5010 := by rw [fixedPC3791]; rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3764 = 5013 := by
  calc
    Artifact.submissionArtifact.instructionPC 3764 =
        Artifact.submissionArtifact.instructionPC 3763 + (YulEvmCompiler.Instr.push 2 9408).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3763 _ (by rfl)
    _ = 5013 := by rw [fixedPC3792]; rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3765 = 5014 := by
  calc
    Artifact.submissionArtifact.instructionPC 3765 =
        Artifact.submissionArtifact.instructionPC 3764 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3764 _ (by rfl)
    _ = 5014 := by rw [fixedPC3793]; rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3766 = 5015 := by
  calc
    Artifact.submissionArtifact.instructionPC 3766 =
        Artifact.submissionArtifact.instructionPC 3765 + (YulEvmCompiler.Instr.op (.Dup ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3765 _ (by rfl)
    _ = 5015 := by rw [fixedPC3794]; rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3767 = 5018 := by
  calc
    Artifact.submissionArtifact.instructionPC 3767 =
        Artifact.submissionArtifact.instructionPC 3766 + (YulEvmCompiler.Instr.push 2 7168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3766 _ (by rfl)
    _ = 5018 := by rw [fixedPC3795]; rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3768 = 5019 := by
  calc
    Artifact.submissionArtifact.instructionPC 3768 =
        Artifact.submissionArtifact.instructionPC 3767 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3767 _ (by rfl)
    _ = 5019 := by rw [fixedPC3796]; rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3769 = 5022 := by
  calc
    Artifact.submissionArtifact.instructionPC 3769 =
        Artifact.submissionArtifact.instructionPC 3768 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3768 _ (by rfl)
    _ = 5022 := by rw [fixedPC3797]; rfl

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3770 = 5023 := by
  calc
    Artifact.submissionArtifact.instructionPC 3770 =
        Artifact.submissionArtifact.instructionPC 3769 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3769 _ (by rfl)
    _ = 5023 := by rw [fixedPC3798]; rfl

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3771 = 5024 := by
  calc
    Artifact.submissionArtifact.instructionPC 3771 =
        Artifact.submissionArtifact.instructionPC 3770 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3770 _ (by rfl)
    _ = 5024 := by rw [fixedPC3799]; rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3772 = 5025 := by
  calc
    Artifact.submissionArtifact.instructionPC 3772 =
        Artifact.submissionArtifact.instructionPC 3771 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3771 _ (by rfl)
    _ = 5025 := by rw [fixedPC3800]; rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3773 = 5026 := by
  calc
    Artifact.submissionArtifact.instructionPC 3773 =
        Artifact.submissionArtifact.instructionPC 3772 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3772 _ (by rfl)
    _ = 5026 := by rw [fixedPC3801]; rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3774 = 5029 := by
  calc
    Artifact.submissionArtifact.instructionPC 3774 =
        Artifact.submissionArtifact.instructionPC 3773 + (YulEvmCompiler.Instr.push 2 2144).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3773 _ (by rfl)
    _ = 5029 := by rw [fixedPC3802]; rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3775 = 5030 := by
  calc
    Artifact.submissionArtifact.instructionPC 3775 =
        Artifact.submissionArtifact.instructionPC 3774 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3774 _ (by rfl)
    _ = 5030 := by rw [fixedPC3803]; rfl

@[simp] theorem fixedJump5023 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5030 = true := by
  simpa only [Artifact.instructionPC, fixedPC3804] using Artifact.isValidJumpDest_index 3775 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3776 = 5031 := by
  calc
    Artifact.submissionArtifact.instructionPC 3776 =
        Artifact.submissionArtifact.instructionPC 3775 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3775 _ (by rfl)
    _ = 5031 := by rw [fixedPC3804]; rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3777 = 5034 := by
  calc
    Artifact.submissionArtifact.instructionPC 3777 =
        Artifact.submissionArtifact.instructionPC 3776 + (YulEvmCompiler.Instr.push 2 8480).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3776 _ (by rfl)
    _ = 5034 := by rw [fixedPC3805]; rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3778 = 5035 := by
  calc
    Artifact.submissionArtifact.instructionPC 3778 =
        Artifact.submissionArtifact.instructionPC 3777 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3777 _ (by rfl)
    _ = 5035 := by rw [fixedPC3806]; rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3779 = 5037 := by
  calc
    Artifact.submissionArtifact.instructionPC 3779 =
        Artifact.submissionArtifact.instructionPC 3778 + (YulEvmCompiler.Instr.push 1 224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3778 _ (by rfl)
    _ = 5037 := by rw [fixedPC3807]; rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3780 = 5038 := by
  calc
    Artifact.submissionArtifact.instructionPC 3780 =
        Artifact.submissionArtifact.instructionPC 3779 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3779 _ (by rfl)
    _ = 5038 := by rw [fixedPC3808]; rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3781 = 5039 := by
  calc
    Artifact.submissionArtifact.instructionPC 3781 =
        Artifact.submissionArtifact.instructionPC 3780 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3780 _ (by rfl)
    _ = 5039 := by rw [fixedPC3809]; rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3782 = 5040 := by
  calc
    Artifact.submissionArtifact.instructionPC 3782 =
        Artifact.submissionArtifact.instructionPC 3781 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3781 _ (by rfl)
    _ = 5040 := by rw [fixedPC3810]; rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3783 = 5041 := by
  calc
    Artifact.submissionArtifact.instructionPC 3783 =
        Artifact.submissionArtifact.instructionPC 3782 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3782 _ (by rfl)
    _ = 5041 := by rw [fixedPC3811]; rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3784 = 5042 := by
  calc
    Artifact.submissionArtifact.instructionPC 3784 =
        Artifact.submissionArtifact.instructionPC 3783 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3783 _ (by rfl)
    _ = 5042 := by rw [fixedPC3812]; rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3785 = 5043 := by
  calc
    Artifact.submissionArtifact.instructionPC 3785 =
        Artifact.submissionArtifact.instructionPC 3784 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3784 _ (by rfl)
    _ = 5043 := by rw [fixedPC3813]; rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3786 = 5046 := by
  calc
    Artifact.submissionArtifact.instructionPC 3786 =
        Artifact.submissionArtifact.instructionPC 3785 + (YulEvmCompiler.Instr.push 2 7392).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3785 _ (by rfl)
    _ = 5046 := by rw [fixedPC3814]; rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3787 = 5047 := by
  calc
    Artifact.submissionArtifact.instructionPC 3787 =
        Artifact.submissionArtifact.instructionPC 3786 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3786 _ (by rfl)
    _ = 5047 := by rw [fixedPC3815]; rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3788 = 5050 := by
  calc
    Artifact.submissionArtifact.instructionPC 3788 =
        Artifact.submissionArtifact.instructionPC 3787 + (YulEvmCompiler.Instr.push 2 8448).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3787 _ (by rfl)
    _ = 5050 := by rw [fixedPC3816]; rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3789 = 5051 := by
  calc
    Artifact.submissionArtifact.instructionPC 3789 =
        Artifact.submissionArtifact.instructionPC 3788 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3788 _ (by rfl)
    _ = 5051 := by rw [fixedPC3817]; rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3790 = 5053 := by
  calc
    Artifact.submissionArtifact.instructionPC 3790 =
        Artifact.submissionArtifact.instructionPC 3789 + (YulEvmCompiler.Instr.push 1 192).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3789 _ (by rfl)
    _ = 5053 := by rw [fixedPC3818]; rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3791 = 5054 := by
  calc
    Artifact.submissionArtifact.instructionPC 3791 =
        Artifact.submissionArtifact.instructionPC 3790 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3790 _ (by rfl)
    _ = 5054 := by rw [fixedPC3819]; rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3792 = 5055 := by
  calc
    Artifact.submissionArtifact.instructionPC 3792 =
        Artifact.submissionArtifact.instructionPC 3791 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3791 _ (by rfl)
    _ = 5055 := by rw [fixedPC3820]; rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3793 = 5056 := by
  calc
    Artifact.submissionArtifact.instructionPC 3793 =
        Artifact.submissionArtifact.instructionPC 3792 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3792 _ (by rfl)
    _ = 5056 := by rw [fixedPC3821]; rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3794 = 5057 := by
  calc
    Artifact.submissionArtifact.instructionPC 3794 =
        Artifact.submissionArtifact.instructionPC 3793 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3793 _ (by rfl)
    _ = 5057 := by rw [fixedPC3822]; rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3795 = 5058 := by
  calc
    Artifact.submissionArtifact.instructionPC 3795 =
        Artifact.submissionArtifact.instructionPC 3794 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3794 _ (by rfl)
    _ = 5058 := by rw [fixedPC3823]; rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3796 = 5059 := by
  calc
    Artifact.submissionArtifact.instructionPC 3796 =
        Artifact.submissionArtifact.instructionPC 3795 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3795 _ (by rfl)
    _ = 5059 := by rw [fixedPC3824]; rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3797 = 5060 := by
  calc
    Artifact.submissionArtifact.instructionPC 3797 =
        Artifact.submissionArtifact.instructionPC 3796 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3796 _ (by rfl)
    _ = 5060 := by rw [fixedPC3825]; rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3798 = 5061 := by
  calc
    Artifact.submissionArtifact.instructionPC 3798 =
        Artifact.submissionArtifact.instructionPC 3797 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3797 _ (by rfl)
    _ = 5061 := by rw [fixedPC3826]; rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3799 = 5062 := by
  calc
    Artifact.submissionArtifact.instructionPC 3799 =
        Artifact.submissionArtifact.instructionPC 3798 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3798 _ (by rfl)
    _ = 5062 := by rw [fixedPC3827]; rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3800 = 5063 := by
  calc
    Artifact.submissionArtifact.instructionPC 3800 =
        Artifact.submissionArtifact.instructionPC 3799 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3799 _ (by rfl)
    _ = 5063 := by rw [fixedPC3828]; rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3801 = 5064 := by
  calc
    Artifact.submissionArtifact.instructionPC 3801 =
        Artifact.submissionArtifact.instructionPC 3800 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3800 _ (by rfl)
    _ = 5064 := by rw [fixedPC3829]; rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3802 = 5065 := by
  calc
    Artifact.submissionArtifact.instructionPC 3802 =
        Artifact.submissionArtifact.instructionPC 3801 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3801 _ (by rfl)
    _ = 5065 := by rw [fixedPC3830]; rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3803 = 5066 := by
  calc
    Artifact.submissionArtifact.instructionPC 3803 =
        Artifact.submissionArtifact.instructionPC 3802 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3802 _ (by rfl)
    _ = 5066 := by rw [fixedPC3831]; rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3804 = 5069 := by
  calc
    Artifact.submissionArtifact.instructionPC 3804 =
        Artifact.submissionArtifact.instructionPC 3803 + (YulEvmCompiler.Instr.push 2 7360).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3803 _ (by rfl)
    _ = 5069 := by rw [fixedPC3832]; rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3805 = 5070 := by
  calc
    Artifact.submissionArtifact.instructionPC 3805 =
        Artifact.submissionArtifact.instructionPC 3804 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3804 _ (by rfl)
    _ = 5070 := by rw [fixedPC3833]; rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3806 = 5073 := by
  calc
    Artifact.submissionArtifact.instructionPC 3806 =
        Artifact.submissionArtifact.instructionPC 3805 + (YulEvmCompiler.Instr.push 2 8416).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3805 _ (by rfl)
    _ = 5073 := by rw [fixedPC3834]; rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3807 = 5074 := by
  calc
    Artifact.submissionArtifact.instructionPC 3807 =
        Artifact.submissionArtifact.instructionPC 3806 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3806 _ (by rfl)
    _ = 5074 := by rw [fixedPC3835]; rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3808 = 5076 := by
  calc
    Artifact.submissionArtifact.instructionPC 3808 =
        Artifact.submissionArtifact.instructionPC 3807 + (YulEvmCompiler.Instr.push 1 160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3807 _ (by rfl)
    _ = 5076 := by rw [fixedPC3836]; rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3809 = 5077 := by
  calc
    Artifact.submissionArtifact.instructionPC 3809 =
        Artifact.submissionArtifact.instructionPC 3808 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3808 _ (by rfl)
    _ = 5077 := by rw [fixedPC3837]; rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3810 = 5078 := by
  calc
    Artifact.submissionArtifact.instructionPC 3810 =
        Artifact.submissionArtifact.instructionPC 3809 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3809 _ (by rfl)
    _ = 5078 := by rw [fixedPC3838]; rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3811 = 5079 := by
  calc
    Artifact.submissionArtifact.instructionPC 3811 =
        Artifact.submissionArtifact.instructionPC 3810 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3810 _ (by rfl)
    _ = 5079 := by rw [fixedPC3839]; rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3812 = 5080 := by
  calc
    Artifact.submissionArtifact.instructionPC 3812 =
        Artifact.submissionArtifact.instructionPC 3811 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3811 _ (by rfl)
    _ = 5080 := by rw [fixedPC3840]; rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3813 = 5081 := by
  calc
    Artifact.submissionArtifact.instructionPC 3813 =
        Artifact.submissionArtifact.instructionPC 3812 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3812 _ (by rfl)
    _ = 5081 := by rw [fixedPC3841]; rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3814 = 5082 := by
  calc
    Artifact.submissionArtifact.instructionPC 3814 =
        Artifact.submissionArtifact.instructionPC 3813 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3813 _ (by rfl)
    _ = 5082 := by rw [fixedPC3842]; rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3815 = 5083 := by
  calc
    Artifact.submissionArtifact.instructionPC 3815 =
        Artifact.submissionArtifact.instructionPC 3814 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3814 _ (by rfl)
    _ = 5083 := by rw [fixedPC3843]; rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3816 = 5084 := by
  calc
    Artifact.submissionArtifact.instructionPC 3816 =
        Artifact.submissionArtifact.instructionPC 3815 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3815 _ (by rfl)
    _ = 5084 := by rw [fixedPC3844]; rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3817 = 5085 := by
  calc
    Artifact.submissionArtifact.instructionPC 3817 =
        Artifact.submissionArtifact.instructionPC 3816 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3816 _ (by rfl)
    _ = 5085 := by rw [fixedPC3845]; rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3818 = 5086 := by
  calc
    Artifact.submissionArtifact.instructionPC 3818 =
        Artifact.submissionArtifact.instructionPC 3817 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3817 _ (by rfl)
    _ = 5086 := by rw [fixedPC3846]; rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3819 = 5087 := by
  calc
    Artifact.submissionArtifact.instructionPC 3819 =
        Artifact.submissionArtifact.instructionPC 3818 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3818 _ (by rfl)
    _ = 5087 := by rw [fixedPC3847]; rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3820 = 5088 := by
  calc
    Artifact.submissionArtifact.instructionPC 3820 =
        Artifact.submissionArtifact.instructionPC 3819 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3819 _ (by rfl)
    _ = 5088 := by rw [fixedPC3848]; rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3821 = 5089 := by
  calc
    Artifact.submissionArtifact.instructionPC 3821 =
        Artifact.submissionArtifact.instructionPC 3820 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3820 _ (by rfl)
    _ = 5089 := by rw [fixedPC3849]; rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3822 = 5092 := by
  calc
    Artifact.submissionArtifact.instructionPC 3822 =
        Artifact.submissionArtifact.instructionPC 3821 + (YulEvmCompiler.Instr.push 2 7328).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3821 _ (by rfl)
    _ = 5092 := by rw [fixedPC3850]; rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3823 = 5093 := by
  calc
    Artifact.submissionArtifact.instructionPC 3823 =
        Artifact.submissionArtifact.instructionPC 3822 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3822 _ (by rfl)
    _ = 5093 := by rw [fixedPC3851]; rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3824 = 5096 := by
  calc
    Artifact.submissionArtifact.instructionPC 3824 =
        Artifact.submissionArtifact.instructionPC 3823 + (YulEvmCompiler.Instr.push 2 8384).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3823 _ (by rfl)
    _ = 5096 := by rw [fixedPC3852]; rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3825 = 5097 := by
  calc
    Artifact.submissionArtifact.instructionPC 3825 =
        Artifact.submissionArtifact.instructionPC 3824 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3824 _ (by rfl)
    _ = 5097 := by rw [fixedPC3853]; rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3826 = 5099 := by
  calc
    Artifact.submissionArtifact.instructionPC 3826 =
        Artifact.submissionArtifact.instructionPC 3825 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3825 _ (by rfl)
    _ = 5099 := by rw [fixedPC3854]; rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3827 = 5100 := by
  calc
    Artifact.submissionArtifact.instructionPC 3827 =
        Artifact.submissionArtifact.instructionPC 3826 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3826 _ (by rfl)
    _ = 5100 := by rw [fixedPC3855]; rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3828 = 5101 := by
  calc
    Artifact.submissionArtifact.instructionPC 3828 =
        Artifact.submissionArtifact.instructionPC 3827 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3827 _ (by rfl)
    _ = 5101 := by rw [fixedPC3856]; rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3829 = 5102 := by
  calc
    Artifact.submissionArtifact.instructionPC 3829 =
        Artifact.submissionArtifact.instructionPC 3828 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3828 _ (by rfl)
    _ = 5102 := by rw [fixedPC3857]; rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3830 = 5103 := by
  calc
    Artifact.submissionArtifact.instructionPC 3830 =
        Artifact.submissionArtifact.instructionPC 3829 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3829 _ (by rfl)
    _ = 5103 := by rw [fixedPC3858]; rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3831 = 5104 := by
  calc
    Artifact.submissionArtifact.instructionPC 3831 =
        Artifact.submissionArtifact.instructionPC 3830 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3830 _ (by rfl)
    _ = 5104 := by rw [fixedPC3859]; rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3832 = 5105 := by
  calc
    Artifact.submissionArtifact.instructionPC 3832 =
        Artifact.submissionArtifact.instructionPC 3831 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3831 _ (by rfl)
    _ = 5105 := by rw [fixedPC3860]; rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3833 = 5106 := by
  calc
    Artifact.submissionArtifact.instructionPC 3833 =
        Artifact.submissionArtifact.instructionPC 3832 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3832 _ (by rfl)
    _ = 5106 := by rw [fixedPC3861]; rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3834 = 5107 := by
  calc
    Artifact.submissionArtifact.instructionPC 3834 =
        Artifact.submissionArtifact.instructionPC 3833 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3833 _ (by rfl)
    _ = 5107 := by rw [fixedPC3862]; rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3835 = 5108 := by
  calc
    Artifact.submissionArtifact.instructionPC 3835 =
        Artifact.submissionArtifact.instructionPC 3834 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3834 _ (by rfl)
    _ = 5108 := by rw [fixedPC3863]; rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3836 = 5109 := by
  calc
    Artifact.submissionArtifact.instructionPC 3836 =
        Artifact.submissionArtifact.instructionPC 3835 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3835 _ (by rfl)
    _ = 5109 := by rw [fixedPC3864]; rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3837 = 5110 := by
  calc
    Artifact.submissionArtifact.instructionPC 3837 =
        Artifact.submissionArtifact.instructionPC 3836 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3836 _ (by rfl)
    _ = 5110 := by rw [fixedPC3865]; rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3838 = 5111 := by
  calc
    Artifact.submissionArtifact.instructionPC 3838 =
        Artifact.submissionArtifact.instructionPC 3837 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3837 _ (by rfl)
    _ = 5111 := by rw [fixedPC3866]; rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3839 = 5112 := by
  calc
    Artifact.submissionArtifact.instructionPC 3839 =
        Artifact.submissionArtifact.instructionPC 3838 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3838 _ (by rfl)
    _ = 5112 := by rw [fixedPC3867]; rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3840 = 5115 := by
  calc
    Artifact.submissionArtifact.instructionPC 3840 =
        Artifact.submissionArtifact.instructionPC 3839 + (YulEvmCompiler.Instr.push 2 7296).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3839 _ (by rfl)
    _ = 5115 := by rw [fixedPC3868]; rfl

@[simp] theorem fixedPC3870 : Artifact.submissionArtifact.instructionPC 3841 = 5116 := by
  calc
    Artifact.submissionArtifact.instructionPC 3841 =
        Artifact.submissionArtifact.instructionPC 3840 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3840 _ (by rfl)
    _ = 5116 := by rw [fixedPC3869]; rfl

@[simp] theorem fixedJump5109 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5116 = true := by
  simpa only [Artifact.instructionPC, fixedPC3870] using Artifact.isValidJumpDest_index 3841 (by rfl)

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3842 = 5117 := by
  calc
    Artifact.submissionArtifact.instructionPC 3842 =
        Artifact.submissionArtifact.instructionPC 3841 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3841 _ (by rfl)
    _ = 5117 := by rw [fixedPC3870]; rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3843 = 5120 := by
  calc
    Artifact.submissionArtifact.instructionPC 3843 =
        Artifact.submissionArtifact.instructionPC 3842 + (YulEvmCompiler.Instr.push 2 8352).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3842 _ (by rfl)
    _ = 5120 := by rw [fixedPC3871]; rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3844 = 5121 := by
  calc
    Artifact.submissionArtifact.instructionPC 3844 =
        Artifact.submissionArtifact.instructionPC 3843 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3843 _ (by rfl)
    _ = 5121 := by rw [fixedPC3872]; rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3845 = 5123 := by
  calc
    Artifact.submissionArtifact.instructionPC 3845 =
        Artifact.submissionArtifact.instructionPC 3844 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3844 _ (by rfl)
    _ = 5123 := by rw [fixedPC3873]; rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3846 = 5124 := by
  calc
    Artifact.submissionArtifact.instructionPC 3846 =
        Artifact.submissionArtifact.instructionPC 3845 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3845 _ (by rfl)
    _ = 5124 := by rw [fixedPC3874]; rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3847 = 5125 := by
  calc
    Artifact.submissionArtifact.instructionPC 3847 =
        Artifact.submissionArtifact.instructionPC 3846 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3846 _ (by rfl)
    _ = 5125 := by rw [fixedPC3875]; rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3848 = 5126 := by
  calc
    Artifact.submissionArtifact.instructionPC 3848 =
        Artifact.submissionArtifact.instructionPC 3847 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3847 _ (by rfl)
    _ = 5126 := by rw [fixedPC3876]; rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3849 = 5127 := by
  calc
    Artifact.submissionArtifact.instructionPC 3849 =
        Artifact.submissionArtifact.instructionPC 3848 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3848 _ (by rfl)
    _ = 5127 := by rw [fixedPC3877]; rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3850 = 5128 := by
  calc
    Artifact.submissionArtifact.instructionPC 3850 =
        Artifact.submissionArtifact.instructionPC 3849 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3849 _ (by rfl)
    _ = 5128 := by rw [fixedPC3878]; rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3851 = 5129 := by
  calc
    Artifact.submissionArtifact.instructionPC 3851 =
        Artifact.submissionArtifact.instructionPC 3850 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3850 _ (by rfl)
    _ = 5129 := by rw [fixedPC3879]; rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3852 = 5130 := by
  calc
    Artifact.submissionArtifact.instructionPC 3852 =
        Artifact.submissionArtifact.instructionPC 3851 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3851 _ (by rfl)
    _ = 5130 := by rw [fixedPC3880]; rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3853 = 5131 := by
  calc
    Artifact.submissionArtifact.instructionPC 3853 =
        Artifact.submissionArtifact.instructionPC 3852 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3852 _ (by rfl)
    _ = 5131 := by rw [fixedPC3881]; rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3854 = 5132 := by
  calc
    Artifact.submissionArtifact.instructionPC 3854 =
        Artifact.submissionArtifact.instructionPC 3853 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3853 _ (by rfl)
    _ = 5132 := by rw [fixedPC3882]; rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3855 = 5133 := by
  calc
    Artifact.submissionArtifact.instructionPC 3855 =
        Artifact.submissionArtifact.instructionPC 3854 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3854 _ (by rfl)
    _ = 5133 := by rw [fixedPC3883]; rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3856 = 5134 := by
  calc
    Artifact.submissionArtifact.instructionPC 3856 =
        Artifact.submissionArtifact.instructionPC 3855 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3855 _ (by rfl)
    _ = 5134 := by rw [fixedPC3884]; rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3857 = 5135 := by
  calc
    Artifact.submissionArtifact.instructionPC 3857 =
        Artifact.submissionArtifact.instructionPC 3856 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3856 _ (by rfl)
    _ = 5135 := by rw [fixedPC3885]; rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3858 = 5136 := by
  calc
    Artifact.submissionArtifact.instructionPC 3858 =
        Artifact.submissionArtifact.instructionPC 3857 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3857 _ (by rfl)
    _ = 5136 := by rw [fixedPC3886]; rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3859 = 5139 := by
  calc
    Artifact.submissionArtifact.instructionPC 3859 =
        Artifact.submissionArtifact.instructionPC 3858 + (YulEvmCompiler.Instr.push 2 7264).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3858 _ (by rfl)
    _ = 5139 := by rw [fixedPC3887]; rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3860 = 5140 := by
  calc
    Artifact.submissionArtifact.instructionPC 3860 =
        Artifact.submissionArtifact.instructionPC 3859 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3859 _ (by rfl)
    _ = 5140 := by rw [fixedPC3888]; rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5140 = true := by
  simpa only [Artifact.instructionPC, fixedPC3889] using Artifact.isValidJumpDest_index 3860 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3861 = 5141 := by
  calc
    Artifact.submissionArtifact.instructionPC 3861 =
        Artifact.submissionArtifact.instructionPC 3860 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3860 _ (by rfl)
    _ = 5141 := by rw [fixedPC3889]; rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3862 = 5144 := by
  calc
    Artifact.submissionArtifact.instructionPC 3862 =
        Artifact.submissionArtifact.instructionPC 3861 + (YulEvmCompiler.Instr.push 2 8320).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3861 _ (by rfl)
    _ = 5144 := by rw [fixedPC3890]; rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3863 = 5145 := by
  calc
    Artifact.submissionArtifact.instructionPC 3863 =
        Artifact.submissionArtifact.instructionPC 3862 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3862 _ (by rfl)
    _ = 5145 := by rw [fixedPC3891]; rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3864 = 5147 := by
  calc
    Artifact.submissionArtifact.instructionPC 3864 =
        Artifact.submissionArtifact.instructionPC 3863 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3863 _ (by rfl)
    _ = 5147 := by rw [fixedPC3892]; rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3865 = 5148 := by
  calc
    Artifact.submissionArtifact.instructionPC 3865 =
        Artifact.submissionArtifact.instructionPC 3864 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3864 _ (by rfl)
    _ = 5148 := by rw [fixedPC3893]; rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3866 = 5149 := by
  calc
    Artifact.submissionArtifact.instructionPC 3866 =
        Artifact.submissionArtifact.instructionPC 3865 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3865 _ (by rfl)
    _ = 5149 := by rw [fixedPC3894]; rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3867 = 5150 := by
  calc
    Artifact.submissionArtifact.instructionPC 3867 =
        Artifact.submissionArtifact.instructionPC 3866 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3866 _ (by rfl)
    _ = 5150 := by rw [fixedPC3895]; rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3868 = 5151 := by
  calc
    Artifact.submissionArtifact.instructionPC 3868 =
        Artifact.submissionArtifact.instructionPC 3867 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3867 _ (by rfl)
    _ = 5151 := by rw [fixedPC3896]; rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3869 = 5152 := by
  calc
    Artifact.submissionArtifact.instructionPC 3869 =
        Artifact.submissionArtifact.instructionPC 3868 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3868 _ (by rfl)
    _ = 5152 := by rw [fixedPC3897]; rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3870 = 5153 := by
  calc
    Artifact.submissionArtifact.instructionPC 3870 =
        Artifact.submissionArtifact.instructionPC 3869 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3869 _ (by rfl)
    _ = 5153 := by rw [fixedPC3898]; rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3871 = 5154 := by
  calc
    Artifact.submissionArtifact.instructionPC 3871 =
        Artifact.submissionArtifact.instructionPC 3870 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3870 _ (by rfl)
    _ = 5154 := by rw [fixedPC3899]; rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3872 = 5155 := by
  calc
    Artifact.submissionArtifact.instructionPC 3872 =
        Artifact.submissionArtifact.instructionPC 3871 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3871 _ (by rfl)
    _ = 5155 := by rw [fixedPC3900]; rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3873 = 5156 := by
  calc
    Artifact.submissionArtifact.instructionPC 3873 =
        Artifact.submissionArtifact.instructionPC 3872 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3872 _ (by rfl)
    _ = 5156 := by rw [fixedPC3901]; rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3874 = 5157 := by
  calc
    Artifact.submissionArtifact.instructionPC 3874 =
        Artifact.submissionArtifact.instructionPC 3873 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3873 _ (by rfl)
    _ = 5157 := by rw [fixedPC3902]; rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3875 = 5158 := by
  calc
    Artifact.submissionArtifact.instructionPC 3875 =
        Artifact.submissionArtifact.instructionPC 3874 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3874 _ (by rfl)
    _ = 5158 := by rw [fixedPC3903]; rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3876 = 5159 := by
  calc
    Artifact.submissionArtifact.instructionPC 3876 =
        Artifact.submissionArtifact.instructionPC 3875 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3875 _ (by rfl)
    _ = 5159 := by rw [fixedPC3904]; rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3877 = 5160 := by
  calc
    Artifact.submissionArtifact.instructionPC 3877 =
        Artifact.submissionArtifact.instructionPC 3876 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3876 _ (by rfl)
    _ = 5160 := by rw [fixedPC3905]; rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3878 = 5163 := by
  calc
    Artifact.submissionArtifact.instructionPC 3878 =
        Artifact.submissionArtifact.instructionPC 3877 + (YulEvmCompiler.Instr.push 2 7232).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3877 _ (by rfl)
    _ = 5163 := by rw [fixedPC3906]; rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3879 = 5164 := by
  calc
    Artifact.submissionArtifact.instructionPC 3879 =
        Artifact.submissionArtifact.instructionPC 3878 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3878 _ (by rfl)
    _ = 5164 := by rw [fixedPC3907]; rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3880 = 5167 := by
  calc
    Artifact.submissionArtifact.instructionPC 3880 =
        Artifact.submissionArtifact.instructionPC 3879 + (YulEvmCompiler.Instr.push 2 8288).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3879 _ (by rfl)
    _ = 5167 := by rw [fixedPC3908]; rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3881 = 5168 := by
  calc
    Artifact.submissionArtifact.instructionPC 3881 =
        Artifact.submissionArtifact.instructionPC 3880 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3880 _ (by rfl)
    _ = 5168 := by rw [fixedPC3909]; rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3882 = 5170 := by
  calc
    Artifact.submissionArtifact.instructionPC 3882 =
        Artifact.submissionArtifact.instructionPC 3881 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3881 _ (by rfl)
    _ = 5170 := by rw [fixedPC3910]; rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3883 = 5171 := by
  calc
    Artifact.submissionArtifact.instructionPC 3883 =
        Artifact.submissionArtifact.instructionPC 3882 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3882 _ (by rfl)
    _ = 5171 := by rw [fixedPC3911]; rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3884 = 5172 := by
  calc
    Artifact.submissionArtifact.instructionPC 3884 =
        Artifact.submissionArtifact.instructionPC 3883 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3883 _ (by rfl)
    _ = 5172 := by rw [fixedPC3912]; rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3885 = 5173 := by
  calc
    Artifact.submissionArtifact.instructionPC 3885 =
        Artifact.submissionArtifact.instructionPC 3884 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3884 _ (by rfl)
    _ = 5173 := by rw [fixedPC3913]; rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3886 = 5174 := by
  calc
    Artifact.submissionArtifact.instructionPC 3886 =
        Artifact.submissionArtifact.instructionPC 3885 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3885 _ (by rfl)
    _ = 5174 := by rw [fixedPC3914]; rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3887 = 5175 := by
  calc
    Artifact.submissionArtifact.instructionPC 3887 =
        Artifact.submissionArtifact.instructionPC 3886 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3886 _ (by rfl)
    _ = 5175 := by rw [fixedPC3915]; rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3888 = 5176 := by
  calc
    Artifact.submissionArtifact.instructionPC 3888 =
        Artifact.submissionArtifact.instructionPC 3887 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3887 _ (by rfl)
    _ = 5176 := by rw [fixedPC3916]; rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3889 = 5177 := by
  calc
    Artifact.submissionArtifact.instructionPC 3889 =
        Artifact.submissionArtifact.instructionPC 3888 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3888 _ (by rfl)
    _ = 5177 := by rw [fixedPC3917]; rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3890 = 5178 := by
  calc
    Artifact.submissionArtifact.instructionPC 3890 =
        Artifact.submissionArtifact.instructionPC 3889 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3889 _ (by rfl)
    _ = 5178 := by rw [fixedPC3918]; rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3891 = 5179 := by
  calc
    Artifact.submissionArtifact.instructionPC 3891 =
        Artifact.submissionArtifact.instructionPC 3890 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3890 _ (by rfl)
    _ = 5179 := by rw [fixedPC3919]; rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3892 = 5180 := by
  calc
    Artifact.submissionArtifact.instructionPC 3892 =
        Artifact.submissionArtifact.instructionPC 3891 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3891 _ (by rfl)
    _ = 5180 := by rw [fixedPC3920]; rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3893 = 5181 := by
  calc
    Artifact.submissionArtifact.instructionPC 3893 =
        Artifact.submissionArtifact.instructionPC 3892 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3892 _ (by rfl)
    _ = 5181 := by rw [fixedPC3921]; rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3894 = 5182 := by
  calc
    Artifact.submissionArtifact.instructionPC 3894 =
        Artifact.submissionArtifact.instructionPC 3893 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3893 _ (by rfl)
    _ = 5182 := by rw [fixedPC3922]; rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3895 = 5183 := by
  calc
    Artifact.submissionArtifact.instructionPC 3895 =
        Artifact.submissionArtifact.instructionPC 3894 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3894 _ (by rfl)
    _ = 5183 := by rw [fixedPC3923]; rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3896 = 5186 := by
  calc
    Artifact.submissionArtifact.instructionPC 3896 =
        Artifact.submissionArtifact.instructionPC 3895 + (YulEvmCompiler.Instr.push 2 7200).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3895 _ (by rfl)
    _ = 5186 := by rw [fixedPC3924]; rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3897 = 5187 := by
  calc
    Artifact.submissionArtifact.instructionPC 3897 =
        Artifact.submissionArtifact.instructionPC 3896 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3896 _ (by rfl)
    _ = 5187 := by rw [fixedPC3925]; rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3898 = 5190 := by
  calc
    Artifact.submissionArtifact.instructionPC 3898 =
        Artifact.submissionArtifact.instructionPC 3897 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3897 _ (by rfl)
    _ = 5190 := by rw [fixedPC3926]; rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3899 = 5191 := by
  calc
    Artifact.submissionArtifact.instructionPC 3899 =
        Artifact.submissionArtifact.instructionPC 3898 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3898 _ (by rfl)
    _ = 5191 := by rw [fixedPC3927]; rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3900 = 5192 := by
  calc
    Artifact.submissionArtifact.instructionPC 3900 =
        Artifact.submissionArtifact.instructionPC 3899 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3899 _ (by rfl)
    _ = 5192 := by rw [fixedPC3928]; rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3901 = 5193 := by
  calc
    Artifact.submissionArtifact.instructionPC 3901 =
        Artifact.submissionArtifact.instructionPC 3900 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3900 _ (by rfl)
    _ = 5193 := by rw [fixedPC3929]; rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3902 = 5194 := by
  calc
    Artifact.submissionArtifact.instructionPC 3902 =
        Artifact.submissionArtifact.instructionPC 3901 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3901 _ (by rfl)
    _ = 5194 := by rw [fixedPC3930]; rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3903 = 5195 := by
  calc
    Artifact.submissionArtifact.instructionPC 3903 =
        Artifact.submissionArtifact.instructionPC 3902 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3902 _ (by rfl)
    _ = 5195 := by rw [fixedPC3931]; rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3904 = 5196 := by
  calc
    Artifact.submissionArtifact.instructionPC 3904 =
        Artifact.submissionArtifact.instructionPC 3903 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3903 _ (by rfl)
    _ = 5196 := by rw [fixedPC3932]; rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3905 = 5197 := by
  calc
    Artifact.submissionArtifact.instructionPC 3905 =
        Artifact.submissionArtifact.instructionPC 3904 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3904 _ (by rfl)
    _ = 5197 := by rw [fixedPC3933]; rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3906 = 5198 := by
  calc
    Artifact.submissionArtifact.instructionPC 3906 =
        Artifact.submissionArtifact.instructionPC 3905 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3905 _ (by rfl)
    _ = 5198 := by rw [fixedPC3934]; rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3907 = 5199 := by
  calc
    Artifact.submissionArtifact.instructionPC 3907 =
        Artifact.submissionArtifact.instructionPC 3906 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3906 _ (by rfl)
    _ = 5199 := by rw [fixedPC3935]; rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3908 = 5200 := by
  calc
    Artifact.submissionArtifact.instructionPC 3908 =
        Artifact.submissionArtifact.instructionPC 3907 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3907 _ (by rfl)
    _ = 5200 := by rw [fixedPC3936]; rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3909 = 5201 := by
  calc
    Artifact.submissionArtifact.instructionPC 3909 =
        Artifact.submissionArtifact.instructionPC 3908 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3908 _ (by rfl)
    _ = 5201 := by rw [fixedPC3937]; rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3910 = 5202 := by
  calc
    Artifact.submissionArtifact.instructionPC 3910 =
        Artifact.submissionArtifact.instructionPC 3909 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3909 _ (by rfl)
    _ = 5202 := by rw [fixedPC3938]; rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3911 = 5203 := by
  calc
    Artifact.submissionArtifact.instructionPC 3911 =
        Artifact.submissionArtifact.instructionPC 3910 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3910 _ (by rfl)
    _ = 5203 := by rw [fixedPC3939]; rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3912 = 5204 := by
  calc
    Artifact.submissionArtifact.instructionPC 3912 =
        Artifact.submissionArtifact.instructionPC 3911 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3911 _ (by rfl)
    _ = 5204 := by rw [fixedPC3940]; rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3913 = 5205 := by
  calc
    Artifact.submissionArtifact.instructionPC 3913 =
        Artifact.submissionArtifact.instructionPC 3912 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3912 _ (by rfl)
    _ = 5205 := by rw [fixedPC3941]; rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3914 = 5208 := by
  calc
    Artifact.submissionArtifact.instructionPC 3914 =
        Artifact.submissionArtifact.instructionPC 3913 + (YulEvmCompiler.Instr.push 2 7168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3913 _ (by rfl)
    _ = 5208 := by rw [fixedPC3942]; rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3915 = 5209 := by
  calc
    Artifact.submissionArtifact.instructionPC 3915 =
        Artifact.submissionArtifact.instructionPC 3914 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3914 _ (by rfl)
    _ = 5209 := by rw [fixedPC3943]; rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3916 = 5210 := by
  calc
    Artifact.submissionArtifact.instructionPC 3916 =
        Artifact.submissionArtifact.instructionPC 3915 + (YulEvmCompiler.Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3915 _ (by rfl)
    _ = 5210 := by rw [fixedPC3944]; rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3917 = 5213 := by
  calc
    Artifact.submissionArtifact.instructionPC 3917 =
        Artifact.submissionArtifact.instructionPC 3916 + (YulEvmCompiler.Instr.push 2 8224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3916 _ (by rfl)
    _ = 5213 := by rw [fixedPC3945]; rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3918 = 5214 := by
  calc
    Artifact.submissionArtifact.instructionPC 3918 =
        Artifact.submissionArtifact.instructionPC 3917 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3917 _ (by rfl)
    _ = 5214 := by rw [fixedPC3946]; rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3919 = 5215 := by
  calc
    Artifact.submissionArtifact.instructionPC 3919 =
        Artifact.submissionArtifact.instructionPC 3918 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3918 _ (by rfl)
    _ = 5215 := by rw [fixedPC3947]; rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3931 = 5248 := by
  decide

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3931 = 5248 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3932 = 5249 := by
  calc
    Artifact.submissionArtifact.instructionPC 3932 =
        Artifact.submissionArtifact.instructionPC 3931 + (YulEvmCompiler.Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3931 _ (by rfl)
    _ = 5249 := by rw [fixedPC3950]; rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3933 = 5252 := by
  calc
    Artifact.submissionArtifact.instructionPC 3933 =
        Artifact.submissionArtifact.instructionPC 3932 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3932 _ (by rfl)
    _ = 5252 := by rw [fixedPC3951]; rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3934 = 5253 := by
  calc
    Artifact.submissionArtifact.instructionPC 3934 =
        Artifact.submissionArtifact.instructionPC 3933 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3933 _ (by rfl)
    _ = 5253 := by rw [fixedPC3952]; rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3935 = 5256 := by
  calc
    Artifact.submissionArtifact.instructionPC 3935 =
        Artifact.submissionArtifact.instructionPC 3934 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3934 _ (by rfl)
    _ = 5256 := by rw [fixedPC3953]; rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3936 = 5257 := by
  calc
    Artifact.submissionArtifact.instructionPC 3936 =
        Artifact.submissionArtifact.instructionPC 3935 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3935 _ (by rfl)
    _ = 5257 := by rw [fixedPC3954]; rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3937 = 5258 := by
  calc
    Artifact.submissionArtifact.instructionPC 3937 =
        Artifact.submissionArtifact.instructionPC 3936 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3936 _ (by rfl)
    _ = 5258 := by rw [fixedPC3955]; rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3938 = 5259 := by
  calc
    Artifact.submissionArtifact.instructionPC 3938 =
        Artifact.submissionArtifact.instructionPC 3937 + (YulEvmCompiler.Instr.op .MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3937 _ (by rfl)
    _ = 5259 := by rw [fixedPC3956]; rfl

@[simp] theorem fixedPC3958 : Artifact.submissionArtifact.instructionPC 3939 = 5260 := by
  calc
    Artifact.submissionArtifact.instructionPC 3939 =
        Artifact.submissionArtifact.instructionPC 3938 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3938 _ (by rfl)
    _ = 5260 := by rw [fixedPC3957]; rfl

@[simp] theorem fixedJump5224 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5260 = true := by
  simpa only [Artifact.instructionPC, fixedPC3958] using Artifact.isValidJumpDest_index 3939 (by rfl)

@[simp] theorem fixedPC3959 : Artifact.submissionArtifact.instructionPC 3940 = 5261 := by
  calc
    Artifact.submissionArtifact.instructionPC 3940 =
        Artifact.submissionArtifact.instructionPC 3939 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3939 _ (by rfl)
    _ = 5261 := by rw [fixedPC3958]; rfl

@[simp] theorem fixedPC3960 : Artifact.submissionArtifact.instructionPC 3941 = 5262 := by
  calc
    Artifact.submissionArtifact.instructionPC 3941 =
        Artifact.submissionArtifact.instructionPC 3940 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3940 _ (by rfl)
    _ = 5262 := by rw [fixedPC3959]; rfl

@[simp] theorem fixedPC3961 : Artifact.submissionArtifact.instructionPC 3942 = 5263 := by
  calc
    Artifact.submissionArtifact.instructionPC 3942 =
        Artifact.submissionArtifact.instructionPC 3941 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3941 _ (by rfl)
    _ = 5263 := by rw [fixedPC3960]; rfl

@[simp] theorem fixedPC3962 : Artifact.submissionArtifact.instructionPC 3943 = 5265 := by
  calc
    Artifact.submissionArtifact.instructionPC 3943 =
        Artifact.submissionArtifact.instructionPC 3942 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3942 _ (by rfl)
    _ = 5265 := by rw [fixedPC3961]; rfl

@[simp] theorem fixedPC3963 : Artifact.submissionArtifact.instructionPC 3944 = 5266 := by
  calc
    Artifact.submissionArtifact.instructionPC 3944 =
        Artifact.submissionArtifact.instructionPC 3943 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3943 _ (by rfl)
    _ = 5266 := by rw [fixedPC3962]; rfl

@[simp] theorem fixedPC3964 : Artifact.submissionArtifact.instructionPC 3945 = 5268 := by
  calc
    Artifact.submissionArtifact.instructionPC 3945 =
        Artifact.submissionArtifact.instructionPC 3944 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3944 _ (by rfl)
    _ = 5268 := by rw [fixedPC3963]; rfl

@[simp] theorem fixedPC3965 : Artifact.submissionArtifact.instructionPC 3946 = 5269 := by
  calc
    Artifact.submissionArtifact.instructionPC 3946 =
        Artifact.submissionArtifact.instructionPC 3945 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3945 _ (by rfl)
    _ = 5269 := by rw [fixedPC3964]; rfl

@[simp] theorem fixedPC3966 : Artifact.submissionArtifact.instructionPC 3947 = 5271 := by
  calc
    Artifact.submissionArtifact.instructionPC 3947 =
        Artifact.submissionArtifact.instructionPC 3946 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3946 _ (by rfl)
    _ = 5271 := by rw [fixedPC3965]; rfl

@[simp] theorem fixedPC3967 : Artifact.submissionArtifact.instructionPC 3948 = 5272 := by
  calc
    Artifact.submissionArtifact.instructionPC 3948 =
        Artifact.submissionArtifact.instructionPC 3947 + (YulEvmCompiler.Instr.op (.Dup ⟨3, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3947 _ (by rfl)
    _ = 5272 := by rw [fixedPC3966]; rfl

@[simp] theorem fixedPC3968 : Artifact.submissionArtifact.instructionPC 3949 = 5273 := by
  calc
    Artifact.submissionArtifact.instructionPC 3949 =
        Artifact.submissionArtifact.instructionPC 3948 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3948 _ (by rfl)
    _ = 5273 := by rw [fixedPC3967]; rfl

@[simp] theorem fixedPC3969 : Artifact.submissionArtifact.instructionPC 3950 = 5274 := by
  calc
    Artifact.submissionArtifact.instructionPC 3950 =
        Artifact.submissionArtifact.instructionPC 3949 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3949 _ (by rfl)
    _ = 5274 := by rw [fixedPC3968]; rfl

@[simp] theorem fixedPC3970 : Artifact.submissionArtifact.instructionPC 3951 = 5276 := by
  calc
    Artifact.submissionArtifact.instructionPC 3951 =
        Artifact.submissionArtifact.instructionPC 3950 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3950 _ (by rfl)
    _ = 5276 := by rw [fixedPC3969]; rfl

@[simp] theorem fixedPC3971 : Artifact.submissionArtifact.instructionPC 3952 = 5277 := by
  calc
    Artifact.submissionArtifact.instructionPC 3952 =
        Artifact.submissionArtifact.instructionPC 3951 + (YulEvmCompiler.Instr.op .XOR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3951 _ (by rfl)
    _ = 5277 := by rw [fixedPC3970]; rfl

@[simp] theorem fixedPC3972 : Artifact.submissionArtifact.instructionPC 3953 = 5278 := by
  calc
    Artifact.submissionArtifact.instructionPC 3953 =
        Artifact.submissionArtifact.instructionPC 3952 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3952 _ (by rfl)
    _ = 5278 := by rw [fixedPC3971]; rfl

@[simp] theorem fixedPC3973 : Artifact.submissionArtifact.instructionPC 3954 = 5279 := by
  calc
    Artifact.submissionArtifact.instructionPC 3954 =
        Artifact.submissionArtifact.instructionPC 3953 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3953 _ (by rfl)
    _ = 5279 := by rw [fixedPC3972]; rfl

@[simp] theorem fixedPC3974 : Artifact.submissionArtifact.instructionPC 3955 = 5281 := by
  calc
    Artifact.submissionArtifact.instructionPC 3955 =
        Artifact.submissionArtifact.instructionPC 3954 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3954 _ (by rfl)
    _ = 5281 := by rw [fixedPC3973]; rfl

@[simp] theorem fixedPC3975 : Artifact.submissionArtifact.instructionPC 3956 = 5282 := by
  calc
    Artifact.submissionArtifact.instructionPC 3956 =
        Artifact.submissionArtifact.instructionPC 3955 + (YulEvmCompiler.Instr.op .XOR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3955 _ (by rfl)
    _ = 5282 := by rw [fixedPC3974]; rfl

@[simp] theorem fixedPC3976 : Artifact.submissionArtifact.instructionPC 3957 = 5283 := by
  calc
    Artifact.submissionArtifact.instructionPC 3957 =
        Artifact.submissionArtifact.instructionPC 3956 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3956 _ (by rfl)
    _ = 5283 := by rw [fixedPC3975]; rfl

@[simp] theorem fixedPC3977 : Artifact.submissionArtifact.instructionPC 3958 = 5286 := by
  calc
    Artifact.submissionArtifact.instructionPC 3958 =
        Artifact.submissionArtifact.instructionPC 3957 + (YulEvmCompiler.Instr.push 2 5308).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3957 _ (by rfl)
    _ = 5286 := by rw [fixedPC3976]; rfl

@[simp] theorem fixedPC3978 : Artifact.submissionArtifact.instructionPC 3959 = 5287 := by
  calc
    Artifact.submissionArtifact.instructionPC 3959 =
        Artifact.submissionArtifact.instructionPC 3958 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3958 _ (by rfl)
    _ = 5287 := by rw [fixedPC3977]; rfl

@[simp] theorem fixedPC3979 : Artifact.submissionArtifact.instructionPC 3960 = 5288 := by
  calc
    Artifact.submissionArtifact.instructionPC 3960 =
        Artifact.submissionArtifact.instructionPC 3959 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3959 _ (by rfl)
    _ = 5288 := by rw [fixedPC3978]; rfl

@[simp] theorem fixedPC3980 : Artifact.submissionArtifact.instructionPC 3961 = 5290 := by
  calc
    Artifact.submissionArtifact.instructionPC 3961 =
        Artifact.submissionArtifact.instructionPC 3960 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3960 _ (by rfl)
    _ = 5290 := by rw [fixedPC3979]; rfl

@[simp] theorem fixedPC3981 : Artifact.submissionArtifact.instructionPC 3962 = 5291 := by
  calc
    Artifact.submissionArtifact.instructionPC 3962 =
        Artifact.submissionArtifact.instructionPC 3961 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3961 _ (by rfl)
    _ = 5291 := by rw [fixedPC3980]; rfl

@[simp] theorem fixedPC3982 : Artifact.submissionArtifact.instructionPC 3963 = 5292 := by
  calc
    Artifact.submissionArtifact.instructionPC 3963 =
        Artifact.submissionArtifact.instructionPC 3962 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3962 _ (by rfl)
    _ = 5292 := by rw [fixedPC3981]; rfl

@[simp] theorem fixedPC3983 : Artifact.submissionArtifact.instructionPC 3964 = 5293 := by
  calc
    Artifact.submissionArtifact.instructionPC 3964 =
        Artifact.submissionArtifact.instructionPC 3963 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3963 _ (by rfl)
    _ = 5293 := by rw [fixedPC3982]; rfl

@[simp] theorem fixedPC3984 : Artifact.submissionArtifact.instructionPC 3965 = 5294 := by
  calc
    Artifact.submissionArtifact.instructionPC 3965 =
        Artifact.submissionArtifact.instructionPC 3964 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3964 _ (by rfl)
    _ = 5294 := by rw [fixedPC3983]; rfl

@[simp] theorem fixedPC3985 : Artifact.submissionArtifact.instructionPC 3966 = 5297 := by
  calc
    Artifact.submissionArtifact.instructionPC 3966 =
        Artifact.submissionArtifact.instructionPC 3965 + (YulEvmCompiler.Instr.push 2 1186).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3965 _ (by rfl)
    _ = 5297 := by rw [fixedPC3984]; rfl

@[simp] theorem fixedPC3986 : Artifact.submissionArtifact.instructionPC 3967 = 5298 := by
  calc
    Artifact.submissionArtifact.instructionPC 3967 =
        Artifact.submissionArtifact.instructionPC 3966 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3966 _ (by rfl)
    _ = 5298 := by rw [fixedPC3985]; rfl

@[simp] theorem fixedPC3987 : Artifact.submissionArtifact.instructionPC 3968 = 5299 := by
  calc
    Artifact.submissionArtifact.instructionPC 3968 =
        Artifact.submissionArtifact.instructionPC 3967 + (YulEvmCompiler.Instr.op (.Dup ⟨3, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3967 _ (by rfl)
    _ = 5299 := by rw [fixedPC3986]; rfl

@[simp] theorem fixedPC3988 : Artifact.submissionArtifact.instructionPC 3969 = 5301 := by
  calc
    Artifact.submissionArtifact.instructionPC 3969 =
        Artifact.submissionArtifact.instructionPC 3968 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3968 _ (by rfl)
    _ = 5301 := by rw [fixedPC3987]; rfl

@[simp] theorem fixedPC3989 : Artifact.submissionArtifact.instructionPC 3970 = 5302 := by
  calc
    Artifact.submissionArtifact.instructionPC 3970 =
        Artifact.submissionArtifact.instructionPC 3969 + (YulEvmCompiler.Instr.op (.Dup ⟨6, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3969 _ (by rfl)
    _ = 5302 := by rw [fixedPC3988]; rfl

@[simp] theorem fixedPC3990 : Artifact.submissionArtifact.instructionPC 3971 = 5303 := by
  calc
    Artifact.submissionArtifact.instructionPC 3971 =
        Artifact.submissionArtifact.instructionPC 3970 + (YulEvmCompiler.Instr.op (.Dup ⟨8, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3970 _ (by rfl)
    _ = 5303 := by rw [fixedPC3989]; rfl

@[simp] theorem fixedPC3991 : Artifact.submissionArtifact.instructionPC 3972 = 5304 := by
  calc
    Artifact.submissionArtifact.instructionPC 3972 =
        Artifact.submissionArtifact.instructionPC 3971 + (YulEvmCompiler.Instr.op (.Dup ⟨10, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3971 _ (by rfl)
    _ = 5304 := by rw [fixedPC3990]; rfl

@[simp] theorem fixedPC3992 : Artifact.submissionArtifact.instructionPC 3973 = 5307 := by
  calc
    Artifact.submissionArtifact.instructionPC 3973 =
        Artifact.submissionArtifact.instructionPC 3972 + (YulEvmCompiler.Instr.push 2 4892).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3972 _ (by rfl)
    _ = 5307 := by rw [fixedPC3991]; rfl

@[simp] theorem fixedPC3993 : Artifact.submissionArtifact.instructionPC 3974 = 5308 := by
  calc
    Artifact.submissionArtifact.instructionPC 3974 =
        Artifact.submissionArtifact.instructionPC 3973 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3973 _ (by rfl)
    _ = 5308 := by rw [fixedPC3992]; rfl

@[simp] theorem fixedJump5272 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5308 = true := by
  simpa only [Artifact.instructionPC, fixedPC3993] using Artifact.isValidJumpDest_index 3974 (by rfl)

@[simp] theorem fixedPC3994 : Artifact.submissionArtifact.instructionPC 3975 = 5309 := by
  calc
    Artifact.submissionArtifact.instructionPC 3975 =
        Artifact.submissionArtifact.instructionPC 3974 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3974 _ (by rfl)
    _ = 5309 := by rw [fixedPC3993]; rfl

@[simp] theorem fixedPC3995 : Artifact.submissionArtifact.instructionPC 3976 = 5310 := by
  calc
    Artifact.submissionArtifact.instructionPC 3976 =
        Artifact.submissionArtifact.instructionPC 3975 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3975 _ (by rfl)
    _ = 5310 := by rw [fixedPC3994]; rfl

@[simp] theorem fixedPC3996 : Artifact.submissionArtifact.instructionPC 3977 = 5311 := by
  calc
    Artifact.submissionArtifact.instructionPC 3977 =
        Artifact.submissionArtifact.instructionPC 3976 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3976 _ (by rfl)
    _ = 5311 := by rw [fixedPC3995]; rfl

@[simp] theorem fixedPC3997 : Artifact.submissionArtifact.instructionPC 3978 = 5312 := by
  calc
    Artifact.submissionArtifact.instructionPC 3978 =
        Artifact.submissionArtifact.instructionPC 3977 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3977 _ (by rfl)
    _ = 5312 := by rw [fixedPC3996]; rfl

@[simp] theorem fixedPC3998 : Artifact.submissionArtifact.instructionPC 3979 = 5315 := by
  calc
    Artifact.submissionArtifact.instructionPC 3979 =
        Artifact.submissionArtifact.instructionPC 3978 + (YulEvmCompiler.Instr.push 2 1233).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3978 _ (by rfl)
    _ = 5315 := by rw [fixedPC3997]; rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 2932 = 3881 := by
  decide

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3881 = true := by
  simpa only [Artifact.instructionPC, fixedPC3999] using Artifact.isValidJumpDest_index 2932 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 2933 = 3882 := by
  calc
    Artifact.submissionArtifact.instructionPC 2933 =
        Artifact.submissionArtifact.instructionPC 2932 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2932 _ (by rfl)
    _ = 3882 := by rw [fixedPC3999]; rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 2934 = 3885 := by
  calc
    Artifact.submissionArtifact.instructionPC 2934 =
        Artifact.submissionArtifact.instructionPC 2933 + (YulEvmCompiler.Instr.push 2 8352).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2933 _ (by rfl)
    _ = 3885 := by rw [fixedPC4000]; rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 2935 = 3886 := by
  calc
    Artifact.submissionArtifact.instructionPC 2935 =
        Artifact.submissionArtifact.instructionPC 2934 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2934 _ (by rfl)
    _ = 3886 := by rw [fixedPC4001]; rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 2936 = 3888 := by
  calc
    Artifact.submissionArtifact.instructionPC 2936 =
        Artifact.submissionArtifact.instructionPC 2935 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2935 _ (by rfl)
    _ = 3888 := by rw [fixedPC4002]; rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 2937 = 3889 := by
  calc
    Artifact.submissionArtifact.instructionPC 2937 =
        Artifact.submissionArtifact.instructionPC 2936 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2936 _ (by rfl)
    _ = 3889 := by rw [fixedPC4003]; rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 2938 = 3890 := by
  calc
    Artifact.submissionArtifact.instructionPC 2938 =
        Artifact.submissionArtifact.instructionPC 2937 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2937 _ (by rfl)
    _ = 3890 := by rw [fixedPC4004]; rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 2939 = 3891 := by
  calc
    Artifact.submissionArtifact.instructionPC 2939 =
        Artifact.submissionArtifact.instructionPC 2938 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2938 _ (by rfl)
    _ = 3891 := by rw [fixedPC4005]; rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 2940 = 3892 := by
  calc
    Artifact.submissionArtifact.instructionPC 2940 =
        Artifact.submissionArtifact.instructionPC 2939 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2939 _ (by rfl)
    _ = 3892 := by rw [fixedPC4006]; rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 2941 = 3893 := by
  calc
    Artifact.submissionArtifact.instructionPC 2941 =
        Artifact.submissionArtifact.instructionPC 2940 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2940 _ (by rfl)
    _ = 3893 := by rw [fixedPC4007]; rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 2942 = 3894 := by
  calc
    Artifact.submissionArtifact.instructionPC 2942 =
        Artifact.submissionArtifact.instructionPC 2941 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2941 _ (by rfl)
    _ = 3894 := by rw [fixedPC4008]; rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 2943 = 3897 := by
  calc
    Artifact.submissionArtifact.instructionPC 2943 =
        Artifact.submissionArtifact.instructionPC 2942 + (YulEvmCompiler.Instr.push 2 7264).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2942 _ (by rfl)
    _ = 3897 := by rw [fixedPC4009]; rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 2944 = 3898 := by
  calc
    Artifact.submissionArtifact.instructionPC 2944 =
        Artifact.submissionArtifact.instructionPC 2943 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2943 _ (by rfl)
    _ = 3898 := by rw [fixedPC4010]; rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 2945 = 3901 := by
  calc
    Artifact.submissionArtifact.instructionPC 2945 =
        Artifact.submissionArtifact.instructionPC 2944 + (YulEvmCompiler.Instr.push 2 5140).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2944 _ (by rfl)
    _ = 3901 := by rw [fixedPC4011]; rfl


@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2882 = 3810 := by rfl
@[simp] theorem earlyExtraPC2881 : Artifact.submissionArtifact.instructionPC 2883 = 3811 := by rfl
@[simp] theorem earlyExtraPC2882 : Artifact.submissionArtifact.instructionPC 2884 = 3814 := by rfl
@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 2885 = 3815 := by rfl
@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 2886 = 3816 := by rfl
@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 2887 = 3817 := by rfl
@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 2888 = 3818 := by rfl
@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 2889 = 3825 := by rfl
@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 2890 = 3826 := by rfl
@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 2891 = 3827 := by rfl
@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 2892 = 3828 := by rfl
@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 2893 = 3831 := by rfl
@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 2894 = 3832 := by rfl
@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 2895 = 3833 := by rfl
@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 2896 = 3836 := by rfl
@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 2897 = 3837 := by rfl
@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 2898 = 3840 := by rfl
@[simp] theorem earlyExtraPC2897 : Artifact.submissionArtifact.instructionPC 2899 = 3841 := by rfl
@[simp] theorem earlyExtraPC2927 : Artifact.submissionArtifact.instructionPC 2929 = 3876 := by rfl
@[simp] theorem earlyExtraPC2928 : Artifact.submissionArtifact.instructionPC 2930 = 3877 := by rfl
@[simp] theorem earlyExtraPC2929 : Artifact.submissionArtifact.instructionPC 2931 = 3880 := by rfl
@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 2932 = 3881 := by rfl
@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 2933 = 3882 := by rfl
@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 2934 = 3885 := by rfl
@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 2935 = 3886 := by rfl
@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 2936 = 3888 := by rfl
@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 2937 = 3889 := by rfl
@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 2938 = 3890 := by rfl
@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 2939 = 3891 := by rfl
@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 2940 = 3892 := by rfl
@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 2941 = 3893 := by rfl
@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 2942 = 3894 := by rfl
@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 2943 = 3897 := by rfl
@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 2944 = 3898 := by rfl
@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 2945 = 3901 := by rfl
@[simp] theorem earlyExtraPC2944 : Artifact.submissionArtifact.instructionPC 2946 = 3902 := by rfl
@[simp] theorem earlyExtraPC3918 : Artifact.submissionArtifact.instructionPC 3920 = 5218 := by rfl
@[simp] theorem earlyExtraPC3919 : Artifact.submissionArtifact.instructionPC 3921 = 5219 := by rfl
@[simp] theorem earlyExtraPC3920 : Artifact.submissionArtifact.instructionPC 3922 = 5222 := by rfl
@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 3923 = 5223 := by rfl
@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 3924 = 5224 := by rfl
@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 3925 = 5240 := by rfl
@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 3926 = 5243 := by rfl
@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 3927 = 5244 := by rfl
@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 3928 = 5245 := by rfl
@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 3929 = 5246 := by rfl
@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 3930 = 5247 := by rfl
end Challenge.Modexp.Submission.Proofs.Fast
