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
  [opAt 1617 .JUMPDEST,
   pushAt 1618 2 4969,
   opAt 1619 .JUMP,
   opAt 3773 .JUMPDEST,
   pushAt 3774 0 0,
   pushAt 3775 2 9344,
   opAt 3776 .MLOAD,
   pushAt 3777 2 256,
   opAt 3778 .EQ,
   pushAt 3779 2 5019,
   opAt 3780 .JUMPI,
   pushAt 3781 2 9344,
   opAt 3782 .MLOAD,
   pushAt 3783 1 128,
   opAt 3784 .EQ,
   pushAt 3785 2 5128,
   opAt 3786 .JUMPI,
   opAt 3787 .POP,
   pushAt 3788 2 9440,
   opAt 3789 .MLOAD,
   pushAt 3790 2 9408,
   opAt 3791 .MLOAD,
   opAt 3792 (.Dup ⟨0, by decide⟩),
   pushAt 3793 2 7168,
   opAt 3794 .ADD,
   pushAt 3795 2 8256,
   opAt 3796 .POP,
   opAt 3797 (.Swap ⟨0, by decide⟩),
   pushAt 3798 0 0,
   opAt 3799 (.Swap ⟨2, by decide⟩),
   pushAt 3800 2 2225,
   opAt 3801 .JUMP]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1617 .JUMPDEST,
   pushAt 1618 2 4969,
   opAt 1619 .JUMP,
   opAt 3773 .JUMPDEST,
   pushAt 3774 0 0,
   pushAt 3775 2 9344,
   opAt 3776 .MLOAD,
   pushAt 3777 2 256,
   opAt 3778 .EQ,
   pushAt 3779 2 5019,
   opAt 3780 .JUMPI,
   opAt 3802 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1617 .JUMPDEST,
   pushAt 1618 2 4969,
   opAt 1619 .JUMP,
   opAt 3773 .JUMPDEST,
   pushAt 3774 0 0,
   pushAt 3775 2 9344,
   opAt 3776 .MLOAD,
   pushAt 3777 2 256,
   opAt 3778 .EQ,
   pushAt 3779 2 5019,
   opAt 3780 .JUMPI,
   pushAt 3781 2 9344,
   opAt 3782 .MLOAD,
   pushAt 3783 1 128,
   opAt 3784 .EQ,
   pushAt 3785 2 5128,
   opAt 3786 .JUMPI,
   opAt 3891 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3803 2 8480,
   opAt 3804 .MLOAD,
   pushAt 3805 1 224,
   opAt 3806 .MLOAD,
   opAt 3807 (.Dup ⟨1, by decide⟩),
   opAt 3808 (.Dup ⟨1, by decide⟩),
   opAt 3809 .GT,
   opAt 3810 (.Swap ⟨1, by decide⟩),
   opAt 3811 .SUB,
   opAt 3812 (.Dup ⟨2, by decide⟩),
   opAt 3813 (.Dup ⟨1, by decide⟩),
   opAt 3814 .SUB,
   opAt 3815 (.Swap ⟨0, by decide⟩),
   opAt 3816 (.Dup ⟨3, by decide⟩),
   opAt 3817 .GT,
   opAt 3818 (.Swap ⟨0, by decide⟩),
   opAt 3819 (.Swap ⟨1, by decide⟩),
   opAt 3820 .OR,
   opAt 3821 (.Swap ⟨1, by decide⟩),
   opAt 3822 .POP,
   pushAt 3823 2 7392,
   opAt 3824 .MSTORE]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3825 2 8448,
   opAt 3826 .MLOAD,
   pushAt 3827 1 192,
   opAt 3828 .MLOAD,
   opAt 3829 (.Dup ⟨1, by decide⟩),
   opAt 3830 (.Dup ⟨1, by decide⟩),
   opAt 3831 .GT,
   opAt 3832 (.Swap ⟨1, by decide⟩),
   opAt 3833 .SUB,
   opAt 3834 (.Dup ⟨2, by decide⟩),
   opAt 3835 (.Dup ⟨1, by decide⟩),
   opAt 3836 .SUB,
   opAt 3837 (.Swap ⟨0, by decide⟩),
   opAt 3838 (.Dup ⟨3, by decide⟩),
   opAt 3839 .GT,
   opAt 3840 (.Swap ⟨0, by decide⟩),
   opAt 3841 (.Swap ⟨1, by decide⟩),
   opAt 3842 .OR,
   opAt 3843 (.Swap ⟨1, by decide⟩),
   opAt 3844 .POP,
   pushAt 3845 2 7360,
   opAt 3846 .MSTORE]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3847 2 8416,
   opAt 3848 .MLOAD,
   pushAt 3849 1 160,
   opAt 3850 .MLOAD,
   opAt 3851 (.Dup ⟨1, by decide⟩),
   opAt 3852 (.Dup ⟨1, by decide⟩),
   opAt 3853 .GT,
   opAt 3854 (.Swap ⟨1, by decide⟩),
   opAt 3855 .SUB,
   opAt 3856 (.Dup ⟨2, by decide⟩),
   opAt 3857 (.Dup ⟨1, by decide⟩),
   opAt 3858 .SUB,
   opAt 3859 (.Swap ⟨0, by decide⟩),
   opAt 3860 (.Dup ⟨3, by decide⟩),
   opAt 3861 .GT,
   opAt 3862 (.Swap ⟨0, by decide⟩),
   opAt 3863 (.Swap ⟨1, by decide⟩),
   opAt 3864 .OR,
   opAt 3865 (.Swap ⟨1, by decide⟩),
   opAt 3866 .POP,
   pushAt 3867 2 7328,
   opAt 3868 .MSTORE]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3869 2 8384,
   opAt 3870 .MLOAD,
   pushAt 3871 1 128,
   opAt 3872 .MLOAD,
   opAt 3873 (.Dup ⟨1, by decide⟩),
   opAt 3874 (.Dup ⟨1, by decide⟩),
   opAt 3875 .GT,
   opAt 3876 (.Swap ⟨1, by decide⟩),
   opAt 3877 .SUB,
   opAt 3878 (.Dup ⟨2, by decide⟩),
   opAt 3879 (.Dup ⟨1, by decide⟩),
   opAt 3880 .SUB,
   opAt 3881 (.Swap ⟨0, by decide⟩),
   opAt 3882 (.Dup ⟨3, by decide⟩),
   opAt 3883 .GT,
   opAt 3884 (.Swap ⟨0, by decide⟩),
   opAt 3885 (.Swap ⟨1, by decide⟩),
   opAt 3886 .OR,
   opAt 3887 (.Swap ⟨1, by decide⟩),
   opAt 3888 .POP,
   pushAt 3889 2 7296,
   opAt 3890 .MSTORE]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3891 .JUMPDEST,
   pushAt 3892 2 8352,
   opAt 3893 .MLOAD,
   pushAt 3894 1 96,
   opAt 3895 .MLOAD,
   opAt 3896 (.Dup ⟨1, by decide⟩),
   opAt 3897 (.Dup ⟨1, by decide⟩),
   opAt 3898 .GT,
   opAt 3899 (.Swap ⟨1, by decide⟩),
   opAt 3900 .SUB,
   opAt 3901 (.Dup ⟨2, by decide⟩),
   opAt 3902 (.Dup ⟨1, by decide⟩),
   opAt 3903 .SUB,
   opAt 3904 (.Swap ⟨0, by decide⟩),
   opAt 3905 (.Dup ⟨3, by decide⟩),
   opAt 3906 .GT,
   opAt 3907 (.Swap ⟨0, by decide⟩),
   opAt 3908 (.Swap ⟨1, by decide⟩),
   opAt 3909 .OR,
   opAt 3910 (.Swap ⟨1, by decide⟩),
   opAt 3911 .POP,
   pushAt 3912 2 7264,
   opAt 3913 .MSTORE]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3914 2 8320,
   opAt 3915 .MLOAD,
   pushAt 3916 1 64,
   opAt 3917 .MLOAD,
   opAt 3918 (.Dup ⟨1, by decide⟩),
   opAt 3919 (.Dup ⟨1, by decide⟩),
   opAt 3920 .GT,
   opAt 3921 (.Swap ⟨1, by decide⟩),
   opAt 3922 .SUB,
   opAt 3923 (.Dup ⟨2, by decide⟩),
   opAt 3924 (.Dup ⟨1, by decide⟩),
   opAt 3925 .SUB,
   opAt 3926 (.Swap ⟨0, by decide⟩),
   opAt 3927 (.Dup ⟨3, by decide⟩),
   opAt 3928 .GT,
   opAt 3929 (.Swap ⟨0, by decide⟩),
   opAt 3930 (.Swap ⟨1, by decide⟩),
   opAt 3931 .OR,
   opAt 3932 (.Swap ⟨1, by decide⟩),
   opAt 3933 .POP,
   pushAt 3934 2 7232,
   opAt 3935 .MSTORE]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3936 2 8288,
   opAt 3937 .MLOAD,
   pushAt 3938 1 32,
   opAt 3939 .MLOAD,
   opAt 3940 (.Dup ⟨1, by decide⟩),
   opAt 3941 (.Dup ⟨1, by decide⟩),
   opAt 3942 .GT,
   opAt 3943 (.Swap ⟨1, by decide⟩),
   opAt 3944 .SUB,
   opAt 3945 (.Dup ⟨2, by decide⟩),
   opAt 3946 (.Dup ⟨1, by decide⟩),
   opAt 3947 .SUB,
   opAt 3948 (.Swap ⟨0, by decide⟩),
   opAt 3949 (.Dup ⟨3, by decide⟩),
   opAt 3950 .GT,
   opAt 3951 (.Swap ⟨0, by decide⟩),
   opAt 3952 (.Swap ⟨1, by decide⟩),
   opAt 3953 .OR,
   opAt 3954 (.Swap ⟨1, by decide⟩),
   opAt 3955 .POP,
   pushAt 3956 2 7200,
   opAt 3957 .MSTORE]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3958 2 8256,
   opAt 3959 .MLOAD,
   pushAt 3960 0 0,
   opAt 3961 .MLOAD,
   opAt 3962 (.Dup ⟨1, by decide⟩),
   opAt 3963 (.Dup ⟨1, by decide⟩),
   opAt 3964 .GT,
   opAt 3965 (.Swap ⟨1, by decide⟩),
   opAt 3966 .SUB,
   opAt 3967 (.Dup ⟨2, by decide⟩),
   opAt 3968 (.Dup ⟨1, by decide⟩),
   opAt 3969 .SUB,
   opAt 3970 (.Swap ⟨0, by decide⟩),
   opAt 3971 (.Dup ⟨3, by decide⟩),
   opAt 3972 .GT,
   opAt 3973 (.Swap ⟨0, by decide⟩),
   opAt 3974 (.Swap ⟨1, by decide⟩),
   opAt 3975 .OR,
   opAt 3976 (.Swap ⟨1, by decide⟩),
   opAt 3977 .POP,
   pushAt 3978 2 7168,
   opAt 3979 .MSTORE]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3980 .ISZERO,
   pushAt 3981 2 8224,
   opAt 3982 .MLOAD,
   opAt 3983 .OR,
   pushAt 3984 2 1087,
   opAt 3985 .NOT,
   opAt 3986 .MUL,
   pushAt 3987 2 8256,
   opAt 3988 .ADD,
   pushAt 3989 2 9344,
   opAt 3990 .MLOAD,
   opAt 3991 (.Swap ⟨1, by decide⟩),
   opAt 3992 .MCOPY,
   opAt 3993 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3892 2 8352,
   opAt 3893 .MLOAD,
   pushAt 3894 1 96,
   opAt 3895 .MLOAD,
   opAt 3896 (.Dup ⟨1, by decide⟩),
   opAt 3897 (.Dup ⟨1, by decide⟩),
   opAt 3898 .GT,
   opAt 3899 (.Swap ⟨1, by decide⟩),
   opAt 3900 .SUB,
   opAt 3901 (.Dup ⟨2, by decide⟩),
   opAt 3902 (.Dup ⟨1, by decide⟩),
   opAt 3903 .SUB,
   opAt 3904 (.Swap ⟨0, by decide⟩),
   opAt 3905 (.Dup ⟨3, by decide⟩),
   opAt 3906 .GT,
   opAt 3907 (.Swap ⟨0, by decide⟩),
   opAt 3908 (.Swap ⟨1, by decide⟩),
   opAt 3909 .OR,
   opAt 3910 (.Swap ⟨1, by decide⟩),
   opAt 3911 .POP,
   pushAt 3912 2 7264,
   opAt 3913 .MSTORE]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3914 2 8320,
   opAt 3915 .MLOAD,
   pushAt 3916 1 64,
   opAt 3917 .MLOAD,
   opAt 3918 (.Dup ⟨1, by decide⟩),
   opAt 3919 (.Dup ⟨1, by decide⟩),
   opAt 3920 .GT,
   opAt 3921 (.Swap ⟨1, by decide⟩),
   opAt 3922 .SUB,
   opAt 3923 (.Dup ⟨2, by decide⟩),
   opAt 3924 (.Dup ⟨1, by decide⟩),
   opAt 3925 .SUB,
   opAt 3926 (.Swap ⟨0, by decide⟩),
   opAt 3927 (.Dup ⟨3, by decide⟩),
   opAt 3928 .GT,
   opAt 3929 (.Swap ⟨0, by decide⟩),
   opAt 3930 (.Swap ⟨1, by decide⟩),
   opAt 3931 .OR,
   opAt 3932 (.Swap ⟨1, by decide⟩),
   opAt 3933 .POP,
   pushAt 3934 2 7232,
   opAt 3935 .MSTORE]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3936 2 8288,
   opAt 3937 .MLOAD,
   pushAt 3938 1 32,
   opAt 3939 .MLOAD,
   opAt 3940 (.Dup ⟨1, by decide⟩),
   opAt 3941 (.Dup ⟨1, by decide⟩),
   opAt 3942 .GT,
   opAt 3943 (.Swap ⟨1, by decide⟩),
   opAt 3944 .SUB,
   opAt 3945 (.Dup ⟨2, by decide⟩),
   opAt 3946 (.Dup ⟨1, by decide⟩),
   opAt 3947 .SUB,
   opAt 3948 (.Swap ⟨0, by decide⟩),
   opAt 3949 (.Dup ⟨3, by decide⟩),
   opAt 3950 .GT,
   opAt 3951 (.Swap ⟨0, by decide⟩),
   opAt 3952 (.Swap ⟨1, by decide⟩),
   opAt 3953 .OR,
   opAt 3954 (.Swap ⟨1, by decide⟩),
   opAt 3955 .POP,
   pushAt 3956 2 7200,
   opAt 3957 .MSTORE]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3958 2 8256,
   opAt 3959 .MLOAD,
   pushAt 3960 0 0,
   opAt 3961 .MLOAD,
   opAt 3962 (.Dup ⟨1, by decide⟩),
   opAt 3963 (.Dup ⟨1, by decide⟩),
   opAt 3964 .GT,
   opAt 3965 (.Swap ⟨1, by decide⟩),
   opAt 3966 .SUB,
   opAt 3967 (.Dup ⟨2, by decide⟩),
   opAt 3968 (.Dup ⟨1, by decide⟩),
   opAt 3969 .SUB,
   opAt 3970 (.Swap ⟨0, by decide⟩),
   opAt 3971 (.Dup ⟨3, by decide⟩),
   opAt 3972 .GT,
   opAt 3973 (.Swap ⟨0, by decide⟩),
   opAt 3974 (.Swap ⟨1, by decide⟩),
   opAt 3975 .OR,
   opAt 3976 (.Swap ⟨1, by decide⟩),
   opAt 3977 .POP,
   pushAt 3978 2 7168,
   opAt 3979 .MSTORE]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3980 .ISZERO,
   pushAt 3981 2 8224,
   opAt 3982 .MLOAD,
   opAt 3983 .OR,
   pushAt 3984 2 1087,
   opAt 3985 .NOT,
   opAt 3986 .MUL,
   pushAt 3987 2 8256,
   opAt 3988 .ADD,
   pushAt 3989 2 9344,
   opAt 3990 .MLOAD,
   opAt 3991 (.Swap ⟨1, by decide⟩),
   opAt 3992 .MCOPY,
   opAt 3993 .JUMP]

@[simp] theorem csPC1617 : Artifact.submissionArtifact.instructionPC 1617 = 2220 := by simpa using fastPC17 1617 (by decide) (by decide)

@[simp] theorem csJump2220 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2220 = true := by
  simpa only [Artifact.instructionPC, csPC1617] using Artifact.isValidJumpDest_index 1617 (by rfl)

@[simp] theorem csPC1618 : Artifact.submissionArtifact.instructionPC 1618 = 2221 := by
  calc
    Artifact.submissionArtifact.instructionPC 1618 =
        Artifact.submissionArtifact.instructionPC 1617 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1617 _ (by rfl)
    _ = 2221 := by rw [csPC1617]; rfl

@[simp] theorem csPC1619 : Artifact.submissionArtifact.instructionPC 1619 = 2224 := by
  calc
    Artifact.submissionArtifact.instructionPC 1619 =
        Artifact.submissionArtifact.instructionPC 1618 +
          (YulEvmCompiler.Instr.push 2 4969).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1618 _ (by rfl)
    _ = 2224 := by rw [csPC1618]; rfl

@[simp] theorem csPC3806 : Artifact.submissionArtifact.instructionPC 3773 = 4969 := by rfl

@[simp] theorem csJump4972 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4969 = true := by
  simpa only [Artifact.instructionPC, csPC3806] using Artifact.isValidJumpDest_index 3773 (by rfl)

@[simp] theorem csPC3807 : Artifact.submissionArtifact.instructionPC 3774 = 4970 := by
  calc
    Artifact.submissionArtifact.instructionPC 3774 =
        Artifact.submissionArtifact.instructionPC 3773 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3773 _ (by rfl)
    _ = 4970 := by rw [csPC3806]; rfl

@[simp] theorem csPC3808 : Artifact.submissionArtifact.instructionPC 3775 = 4971 := by
  calc
    Artifact.submissionArtifact.instructionPC 3775 =
        Artifact.submissionArtifact.instructionPC 3774 +
          (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3774 _ (by rfl)
    _ = 4971 := by rw [csPC3807]; rfl

@[simp] theorem csPC3809 : Artifact.submissionArtifact.instructionPC 3776 = 4974 := by
  calc
    Artifact.submissionArtifact.instructionPC 3776 =
        Artifact.submissionArtifact.instructionPC 3775 +
          (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3775 _ (by rfl)
    _ = 4974 := by rw [csPC3808]; rfl

@[simp] theorem csPC3810 : Artifact.submissionArtifact.instructionPC 3777 = 4975 := by
  calc
    Artifact.submissionArtifact.instructionPC 3777 =
        Artifact.submissionArtifact.instructionPC 3776 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3776 _ (by rfl)
    _ = 4975 := by rw [csPC3809]; rfl

@[simp] theorem csPC3811 : Artifact.submissionArtifact.instructionPC 3778 = 4978 := by
  calc
    Artifact.submissionArtifact.instructionPC 3778 =
        Artifact.submissionArtifact.instructionPC 3777 +
          (YulEvmCompiler.Instr.push 2 256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3777 _ (by rfl)
    _ = 4978 := by rw [csPC3810]; rfl

@[simp] theorem csPC3812 : Artifact.submissionArtifact.instructionPC 3779 = 4979 := by
  calc
    Artifact.submissionArtifact.instructionPC 3779 =
        Artifact.submissionArtifact.instructionPC 3778 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3778 _ (by rfl)
    _ = 4979 := by rw [csPC3811]; rfl

@[simp] theorem csPC3813 : Artifact.submissionArtifact.instructionPC 3780 = 4982 := by
  calc
    Artifact.submissionArtifact.instructionPC 3780 =
        Artifact.submissionArtifact.instructionPC 3779 +
          (YulEvmCompiler.Instr.push 2 5019).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3779 _ (by rfl)
    _ = 4982 := by rw [csPC3812]; rfl

@[simp] theorem csPC3814 : Artifact.submissionArtifact.instructionPC 3781 = 4983 := by
  calc
    Artifact.submissionArtifact.instructionPC 3781 =
        Artifact.submissionArtifact.instructionPC 3780 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3780 _ (by rfl)
    _ = 4983 := by rw [csPC3813]; rfl

@[simp] theorem csPC3815 : Artifact.submissionArtifact.instructionPC 3782 = 4986 := by
  calc
    Artifact.submissionArtifact.instructionPC 3782 =
        Artifact.submissionArtifact.instructionPC 3781 +
          (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3781 _ (by rfl)
    _ = 4986 := by rw [csPC3814]; rfl

@[simp] theorem csPC3816 : Artifact.submissionArtifact.instructionPC 3783 = 4987 := by
  calc
    Artifact.submissionArtifact.instructionPC 3783 =
        Artifact.submissionArtifact.instructionPC 3782 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3782 _ (by rfl)
    _ = 4987 := by rw [csPC3815]; rfl

@[simp] theorem csPC3817 : Artifact.submissionArtifact.instructionPC 3784 = 4989 := by
  calc
    Artifact.submissionArtifact.instructionPC 3784 =
        Artifact.submissionArtifact.instructionPC 3783 +
          (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3783 _ (by rfl)
    _ = 4989 := by rw [csPC3816]; rfl

@[simp] theorem csPC3818 : Artifact.submissionArtifact.instructionPC 3785 = 4990 := by
  calc
    Artifact.submissionArtifact.instructionPC 3785 =
        Artifact.submissionArtifact.instructionPC 3784 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3784 _ (by rfl)
    _ = 4990 := by rw [csPC3817]; rfl

@[simp] theorem csPC3819 : Artifact.submissionArtifact.instructionPC 3786 = 4993 := by
  calc
    Artifact.submissionArtifact.instructionPC 3786 =
        Artifact.submissionArtifact.instructionPC 3785 +
          (YulEvmCompiler.Instr.push 2 5128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3785 _ (by rfl)
    _ = 4993 := by rw [csPC3818]; rfl

@[simp] theorem csPC3820 : Artifact.submissionArtifact.instructionPC 3787 = 4994 := by
  calc
    Artifact.submissionArtifact.instructionPC 3787 =
        Artifact.submissionArtifact.instructionPC 3786 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3786 _ (by rfl)
    _ = 4994 := by rw [csPC3819]; rfl

@[simp] theorem csPC3821 : Artifact.submissionArtifact.instructionPC 3788 = 4995 := by
  calc
    Artifact.submissionArtifact.instructionPC 3788 =
        Artifact.submissionArtifact.instructionPC 3787 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3787 _ (by rfl)
    _ = 4995 := by rw [csPC3820]; rfl

@[simp] theorem csPC3822 : Artifact.submissionArtifact.instructionPC 3789 = 4998 := by
  calc
    Artifact.submissionArtifact.instructionPC 3789 =
        Artifact.submissionArtifact.instructionPC 3788 +
          (YulEvmCompiler.Instr.push 2 9440).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3788 _ (by rfl)
    _ = 4998 := by rw [csPC3821]; rfl

@[simp] theorem csPC3823 : Artifact.submissionArtifact.instructionPC 3790 = 4999 := by
  calc
    Artifact.submissionArtifact.instructionPC 3790 =
        Artifact.submissionArtifact.instructionPC 3789 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3789 _ (by rfl)
    _ = 4999 := by rw [csPC3822]; rfl

@[simp] theorem csPC3824 : Artifact.submissionArtifact.instructionPC 3791 = 5002 := by
  calc
    Artifact.submissionArtifact.instructionPC 3791 =
        Artifact.submissionArtifact.instructionPC 3790 +
          (YulEvmCompiler.Instr.push 2 9408).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3790 _ (by rfl)
    _ = 5002 := by rw [csPC3823]; rfl

@[simp] theorem csPC3825 : Artifact.submissionArtifact.instructionPC 3792 = 5003 := by
  calc
    Artifact.submissionArtifact.instructionPC 3792 =
        Artifact.submissionArtifact.instructionPC 3791 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3791 _ (by rfl)
    _ = 5003 := by rw [csPC3824]; rfl

@[simp] theorem csPC3826 : Artifact.submissionArtifact.instructionPC 3793 = 5004 := by
  calc
    Artifact.submissionArtifact.instructionPC 3793 =
        Artifact.submissionArtifact.instructionPC 3792 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3792 _ (by rfl)
    _ = 5004 := by rw [csPC3825]; rfl

@[simp] theorem csPC3827 : Artifact.submissionArtifact.instructionPC 3794 = 5007 := by
  calc
    Artifact.submissionArtifact.instructionPC 3794 =
        Artifact.submissionArtifact.instructionPC 3793 +
          (YulEvmCompiler.Instr.push 2 7168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3793 _ (by rfl)
    _ = 5007 := by rw [csPC3826]; rfl

@[simp] theorem csPC3828 : Artifact.submissionArtifact.instructionPC 3795 = 5008 := by
  calc
    Artifact.submissionArtifact.instructionPC 3795 =
        Artifact.submissionArtifact.instructionPC 3794 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3794 _ (by rfl)
    _ = 5008 := by rw [csPC3827]; rfl

@[simp] theorem csPC3829 : Artifact.submissionArtifact.instructionPC 3796 = 5011 := by
  calc
    Artifact.submissionArtifact.instructionPC 3796 =
        Artifact.submissionArtifact.instructionPC 3795 +
          (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3795 _ (by rfl)
    _ = 5011 := by rw [csPC3828]; rfl

@[simp] theorem csPC3830 : Artifact.submissionArtifact.instructionPC 3797 = 5012 := by
  calc
    Artifact.submissionArtifact.instructionPC 3797 =
        Artifact.submissionArtifact.instructionPC 3796 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3796 _ (by rfl)
    _ = 5012 := by rw [csPC3829]; rfl

@[simp] theorem csPC3831 : Artifact.submissionArtifact.instructionPC 3798 = 5013 := by
  calc
    Artifact.submissionArtifact.instructionPC 3798 =
        Artifact.submissionArtifact.instructionPC 3797 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3797 _ (by rfl)
    _ = 5013 := by rw [csPC3830]; rfl

@[simp] theorem csPC3832 : Artifact.submissionArtifact.instructionPC 3799 = 5014 := by
  calc
    Artifact.submissionArtifact.instructionPC 3799 =
        Artifact.submissionArtifact.instructionPC 3798 +
          (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3798 _ (by rfl)
    _ = 5014 := by rw [csPC3831]; rfl

@[simp] theorem csPC3833 : Artifact.submissionArtifact.instructionPC 3800 = 5015 := by
  calc
    Artifact.submissionArtifact.instructionPC 3800 =
        Artifact.submissionArtifact.instructionPC 3799 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3799 _ (by rfl)
    _ = 5015 := by rw [csPC3832]; rfl

@[simp] theorem csPC3834 : Artifact.submissionArtifact.instructionPC 3801 = 5018 := by
  calc
    Artifact.submissionArtifact.instructionPC 3801 =
        Artifact.submissionArtifact.instructionPC 3800 +
          (YulEvmCompiler.Instr.push 2 2225).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3800 _ (by rfl)
    _ = 5018 := by rw [csPC3833]; rfl

@[simp] theorem csPC3835 : Artifact.submissionArtifact.instructionPC 3802 = 5019 := by
  calc
    Artifact.submissionArtifact.instructionPC 3802 =
        Artifact.submissionArtifact.instructionPC 3801 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3801 _ (by rfl)
    _ = 5019 := by rw [csPC3834]; rfl

@[simp] theorem csJump5022 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5019 = true := by
  simpa only [Artifact.instructionPC, csPC3835] using Artifact.isValidJumpDest_index 3802 (by rfl)

@[simp] theorem csPC3836 : Artifact.submissionArtifact.instructionPC 3803 = 5020 := by
  calc
    Artifact.submissionArtifact.instructionPC 3803 =
        Artifact.submissionArtifact.instructionPC 3802 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3802 _ (by rfl)
    _ = 5020 := by rw [csPC3835]; rfl

@[simp] theorem csPC3837 : Artifact.submissionArtifact.instructionPC 3804 = 5023 := by
  calc
    Artifact.submissionArtifact.instructionPC 3804 =
        Artifact.submissionArtifact.instructionPC 3803 +
          (YulEvmCompiler.Instr.push 2 8480).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3803 _ (by rfl)
    _ = 5023 := by rw [csPC3836]; rfl

@[simp] theorem csPC3838 : Artifact.submissionArtifact.instructionPC 3805 = 5024 := by
  calc
    Artifact.submissionArtifact.instructionPC 3805 =
        Artifact.submissionArtifact.instructionPC 3804 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3804 _ (by rfl)
    _ = 5024 := by rw [csPC3837]; rfl

@[simp] theorem csPC3839 : Artifact.submissionArtifact.instructionPC 3806 = 5026 := by
  calc
    Artifact.submissionArtifact.instructionPC 3806 =
        Artifact.submissionArtifact.instructionPC 3805 +
          (YulEvmCompiler.Instr.push 1 224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3805 _ (by rfl)
    _ = 5026 := by rw [csPC3838]; rfl

@[simp] theorem csPC3840 : Artifact.submissionArtifact.instructionPC 3807 = 5027 := by
  calc
    Artifact.submissionArtifact.instructionPC 3807 =
        Artifact.submissionArtifact.instructionPC 3806 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3806 _ (by rfl)
    _ = 5027 := by rw [csPC3839]; rfl

@[simp] theorem csPC3841 : Artifact.submissionArtifact.instructionPC 3808 = 5028 := by
  calc
    Artifact.submissionArtifact.instructionPC 3808 =
        Artifact.submissionArtifact.instructionPC 3807 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3807 _ (by rfl)
    _ = 5028 := by rw [csPC3840]; rfl

@[simp] theorem csPC3842 : Artifact.submissionArtifact.instructionPC 3809 = 5029 := by
  calc
    Artifact.submissionArtifact.instructionPC 3809 =
        Artifact.submissionArtifact.instructionPC 3808 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3808 _ (by rfl)
    _ = 5029 := by rw [csPC3841]; rfl

@[simp] theorem csPC3843 : Artifact.submissionArtifact.instructionPC 3810 = 5030 := by
  calc
    Artifact.submissionArtifact.instructionPC 3810 =
        Artifact.submissionArtifact.instructionPC 3809 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3809 _ (by rfl)
    _ = 5030 := by rw [csPC3842]; rfl

@[simp] theorem csPC3844 : Artifact.submissionArtifact.instructionPC 3811 = 5031 := by
  calc
    Artifact.submissionArtifact.instructionPC 3811 =
        Artifact.submissionArtifact.instructionPC 3810 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3810 _ (by rfl)
    _ = 5031 := by rw [csPC3843]; rfl

@[simp] theorem csPC3845 : Artifact.submissionArtifact.instructionPC 3812 = 5032 := by
  calc
    Artifact.submissionArtifact.instructionPC 3812 =
        Artifact.submissionArtifact.instructionPC 3811 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3811 _ (by rfl)
    _ = 5032 := by rw [csPC3844]; rfl

@[simp] theorem csPC3846 : Artifact.submissionArtifact.instructionPC 3813 = 5033 := by
  calc
    Artifact.submissionArtifact.instructionPC 3813 =
        Artifact.submissionArtifact.instructionPC 3812 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3812 _ (by rfl)
    _ = 5033 := by rw [csPC3845]; rfl

@[simp] theorem csPC3847 : Artifact.submissionArtifact.instructionPC 3814 = 5034 := by
  calc
    Artifact.submissionArtifact.instructionPC 3814 =
        Artifact.submissionArtifact.instructionPC 3813 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3813 _ (by rfl)
    _ = 5034 := by rw [csPC3846]; rfl

@[simp] theorem csPC3848 : Artifact.submissionArtifact.instructionPC 3815 = 5035 := by
  calc
    Artifact.submissionArtifact.instructionPC 3815 =
        Artifact.submissionArtifact.instructionPC 3814 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3814 _ (by rfl)
    _ = 5035 := by rw [csPC3847]; rfl

@[simp] theorem csPC3849 : Artifact.submissionArtifact.instructionPC 3816 = 5036 := by
  calc
    Artifact.submissionArtifact.instructionPC 3816 =
        Artifact.submissionArtifact.instructionPC 3815 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3815 _ (by rfl)
    _ = 5036 := by rw [csPC3848]; rfl

@[simp] theorem csPC3850 : Artifact.submissionArtifact.instructionPC 3817 = 5037 := by
  calc
    Artifact.submissionArtifact.instructionPC 3817 =
        Artifact.submissionArtifact.instructionPC 3816 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3816 _ (by rfl)
    _ = 5037 := by rw [csPC3849]; rfl

@[simp] theorem csPC3851 : Artifact.submissionArtifact.instructionPC 3818 = 5038 := by
  calc
    Artifact.submissionArtifact.instructionPC 3818 =
        Artifact.submissionArtifact.instructionPC 3817 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3817 _ (by rfl)
    _ = 5038 := by rw [csPC3850]; rfl

@[simp] theorem csPC3852 : Artifact.submissionArtifact.instructionPC 3819 = 5039 := by
  calc
    Artifact.submissionArtifact.instructionPC 3819 =
        Artifact.submissionArtifact.instructionPC 3818 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3818 _ (by rfl)
    _ = 5039 := by rw [csPC3851]; rfl

@[simp] theorem csPC3853 : Artifact.submissionArtifact.instructionPC 3820 = 5040 := by
  calc
    Artifact.submissionArtifact.instructionPC 3820 =
        Artifact.submissionArtifact.instructionPC 3819 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3819 _ (by rfl)
    _ = 5040 := by rw [csPC3852]; rfl

@[simp] theorem csPC3854 : Artifact.submissionArtifact.instructionPC 3821 = 5041 := by
  calc
    Artifact.submissionArtifact.instructionPC 3821 =
        Artifact.submissionArtifact.instructionPC 3820 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3820 _ (by rfl)
    _ = 5041 := by rw [csPC3853]; rfl

@[simp] theorem csPC3855 : Artifact.submissionArtifact.instructionPC 3822 = 5042 := by
  calc
    Artifact.submissionArtifact.instructionPC 3822 =
        Artifact.submissionArtifact.instructionPC 3821 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3821 _ (by rfl)
    _ = 5042 := by rw [csPC3854]; rfl

@[simp] theorem csPC3856 : Artifact.submissionArtifact.instructionPC 3823 = 5043 := by
  calc
    Artifact.submissionArtifact.instructionPC 3823 =
        Artifact.submissionArtifact.instructionPC 3822 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3822 _ (by rfl)
    _ = 5043 := by rw [csPC3855]; rfl

@[simp] theorem csPC3857 : Artifact.submissionArtifact.instructionPC 3824 = 5046 := by
  calc
    Artifact.submissionArtifact.instructionPC 3824 =
        Artifact.submissionArtifact.instructionPC 3823 +
          (YulEvmCompiler.Instr.push 2 7392).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3823 _ (by rfl)
    _ = 5046 := by rw [csPC3856]; rfl

@[simp] theorem csPC3858 : Artifact.submissionArtifact.instructionPC 3825 = 5047 := by
  calc
    Artifact.submissionArtifact.instructionPC 3825 =
        Artifact.submissionArtifact.instructionPC 3824 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3824 _ (by rfl)
    _ = 5047 := by rw [csPC3857]; rfl

@[simp] theorem csPC3859 : Artifact.submissionArtifact.instructionPC 3826 = 5050 := by
  calc
    Artifact.submissionArtifact.instructionPC 3826 =
        Artifact.submissionArtifact.instructionPC 3825 +
          (YulEvmCompiler.Instr.push 2 8448).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3825 _ (by rfl)
    _ = 5050 := by rw [csPC3858]; rfl

@[simp] theorem csPC3860 : Artifact.submissionArtifact.instructionPC 3827 = 5051 := by
  calc
    Artifact.submissionArtifact.instructionPC 3827 =
        Artifact.submissionArtifact.instructionPC 3826 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3826 _ (by rfl)
    _ = 5051 := by rw [csPC3859]; rfl

@[simp] theorem csPC3861 : Artifact.submissionArtifact.instructionPC 3828 = 5053 := by
  calc
    Artifact.submissionArtifact.instructionPC 3828 =
        Artifact.submissionArtifact.instructionPC 3827 +
          (YulEvmCompiler.Instr.push 1 192).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3827 _ (by rfl)
    _ = 5053 := by rw [csPC3860]; rfl

@[simp] theorem csPC3862 : Artifact.submissionArtifact.instructionPC 3829 = 5054 := by
  calc
    Artifact.submissionArtifact.instructionPC 3829 =
        Artifact.submissionArtifact.instructionPC 3828 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3828 _ (by rfl)
    _ = 5054 := by rw [csPC3861]; rfl

@[simp] theorem csPC3863 : Artifact.submissionArtifact.instructionPC 3830 = 5055 := by
  calc
    Artifact.submissionArtifact.instructionPC 3830 =
        Artifact.submissionArtifact.instructionPC 3829 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3829 _ (by rfl)
    _ = 5055 := by rw [csPC3862]; rfl

@[simp] theorem csPC3864 : Artifact.submissionArtifact.instructionPC 3831 = 5056 := by
  calc
    Artifact.submissionArtifact.instructionPC 3831 =
        Artifact.submissionArtifact.instructionPC 3830 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3830 _ (by rfl)
    _ = 5056 := by rw [csPC3863]; rfl

@[simp] theorem csPC3865 : Artifact.submissionArtifact.instructionPC 3832 = 5057 := by
  calc
    Artifact.submissionArtifact.instructionPC 3832 =
        Artifact.submissionArtifact.instructionPC 3831 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3831 _ (by rfl)
    _ = 5057 := by rw [csPC3864]; rfl

@[simp] theorem csPC3866 : Artifact.submissionArtifact.instructionPC 3833 = 5058 := by
  calc
    Artifact.submissionArtifact.instructionPC 3833 =
        Artifact.submissionArtifact.instructionPC 3832 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3832 _ (by rfl)
    _ = 5058 := by rw [csPC3865]; rfl

@[simp] theorem csPC3867 : Artifact.submissionArtifact.instructionPC 3834 = 5059 := by
  calc
    Artifact.submissionArtifact.instructionPC 3834 =
        Artifact.submissionArtifact.instructionPC 3833 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3833 _ (by rfl)
    _ = 5059 := by rw [csPC3866]; rfl

@[simp] theorem csPC3868 : Artifact.submissionArtifact.instructionPC 3835 = 5060 := by
  calc
    Artifact.submissionArtifact.instructionPC 3835 =
        Artifact.submissionArtifact.instructionPC 3834 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3834 _ (by rfl)
    _ = 5060 := by rw [csPC3867]; rfl

@[simp] theorem csPC3869 : Artifact.submissionArtifact.instructionPC 3836 = 5061 := by
  calc
    Artifact.submissionArtifact.instructionPC 3836 =
        Artifact.submissionArtifact.instructionPC 3835 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3835 _ (by rfl)
    _ = 5061 := by rw [csPC3868]; rfl

@[simp] theorem csPC3870 : Artifact.submissionArtifact.instructionPC 3837 = 5062 := by
  calc
    Artifact.submissionArtifact.instructionPC 3837 =
        Artifact.submissionArtifact.instructionPC 3836 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3836 _ (by rfl)
    _ = 5062 := by rw [csPC3869]; rfl

@[simp] theorem csPC3871 : Artifact.submissionArtifact.instructionPC 3838 = 5063 := by
  calc
    Artifact.submissionArtifact.instructionPC 3838 =
        Artifact.submissionArtifact.instructionPC 3837 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3837 _ (by rfl)
    _ = 5063 := by rw [csPC3870]; rfl

@[simp] theorem csPC3872 : Artifact.submissionArtifact.instructionPC 3839 = 5064 := by
  calc
    Artifact.submissionArtifact.instructionPC 3839 =
        Artifact.submissionArtifact.instructionPC 3838 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3838 _ (by rfl)
    _ = 5064 := by rw [csPC3871]; rfl

@[simp] theorem csPC3873 : Artifact.submissionArtifact.instructionPC 3840 = 5065 := by
  calc
    Artifact.submissionArtifact.instructionPC 3840 =
        Artifact.submissionArtifact.instructionPC 3839 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3839 _ (by rfl)
    _ = 5065 := by rw [csPC3872]; rfl

@[simp] theorem csPC3874 : Artifact.submissionArtifact.instructionPC 3841 = 5066 := by
  calc
    Artifact.submissionArtifact.instructionPC 3841 =
        Artifact.submissionArtifact.instructionPC 3840 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3840 _ (by rfl)
    _ = 5066 := by rw [csPC3873]; rfl

@[simp] theorem csPC3875 : Artifact.submissionArtifact.instructionPC 3842 = 5067 := by
  calc
    Artifact.submissionArtifact.instructionPC 3842 =
        Artifact.submissionArtifact.instructionPC 3841 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3841 _ (by rfl)
    _ = 5067 := by rw [csPC3874]; rfl

@[simp] theorem csPC3876 : Artifact.submissionArtifact.instructionPC 3843 = 5068 := by
  calc
    Artifact.submissionArtifact.instructionPC 3843 =
        Artifact.submissionArtifact.instructionPC 3842 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3842 _ (by rfl)
    _ = 5068 := by rw [csPC3875]; rfl

@[simp] theorem csPC3877 : Artifact.submissionArtifact.instructionPC 3844 = 5069 := by
  calc
    Artifact.submissionArtifact.instructionPC 3844 =
        Artifact.submissionArtifact.instructionPC 3843 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3843 _ (by rfl)
    _ = 5069 := by rw [csPC3876]; rfl

@[simp] theorem csPC3878 : Artifact.submissionArtifact.instructionPC 3845 = 5070 := by
  calc
    Artifact.submissionArtifact.instructionPC 3845 =
        Artifact.submissionArtifact.instructionPC 3844 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3844 _ (by rfl)
    _ = 5070 := by rw [csPC3877]; rfl

@[simp] theorem csPC3879 : Artifact.submissionArtifact.instructionPC 3846 = 5073 := by
  calc
    Artifact.submissionArtifact.instructionPC 3846 =
        Artifact.submissionArtifact.instructionPC 3845 +
          (YulEvmCompiler.Instr.push 2 7360).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3845 _ (by rfl)
    _ = 5073 := by rw [csPC3878]; rfl

@[simp] theorem csPC3880 : Artifact.submissionArtifact.instructionPC 3847 = 5074 := by
  calc
    Artifact.submissionArtifact.instructionPC 3847 =
        Artifact.submissionArtifact.instructionPC 3846 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3846 _ (by rfl)
    _ = 5074 := by rw [csPC3879]; rfl

@[simp] theorem csPC3881 : Artifact.submissionArtifact.instructionPC 3848 = 5077 := by
  calc
    Artifact.submissionArtifact.instructionPC 3848 =
        Artifact.submissionArtifact.instructionPC 3847 +
          (YulEvmCompiler.Instr.push 2 8416).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3847 _ (by rfl)
    _ = 5077 := by rw [csPC3880]; rfl

@[simp] theorem csPC3882 : Artifact.submissionArtifact.instructionPC 3849 = 5078 := by
  calc
    Artifact.submissionArtifact.instructionPC 3849 =
        Artifact.submissionArtifact.instructionPC 3848 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3848 _ (by rfl)
    _ = 5078 := by rw [csPC3881]; rfl

@[simp] theorem csPC3883 : Artifact.submissionArtifact.instructionPC 3850 = 5080 := by
  calc
    Artifact.submissionArtifact.instructionPC 3850 =
        Artifact.submissionArtifact.instructionPC 3849 +
          (YulEvmCompiler.Instr.push 1 160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3849 _ (by rfl)
    _ = 5080 := by rw [csPC3882]; rfl

@[simp] theorem csPC3884 : Artifact.submissionArtifact.instructionPC 3851 = 5081 := by
  calc
    Artifact.submissionArtifact.instructionPC 3851 =
        Artifact.submissionArtifact.instructionPC 3850 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3850 _ (by rfl)
    _ = 5081 := by rw [csPC3883]; rfl

@[simp] theorem csPC3885 : Artifact.submissionArtifact.instructionPC 3852 = 5082 := by
  calc
    Artifact.submissionArtifact.instructionPC 3852 =
        Artifact.submissionArtifact.instructionPC 3851 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3851 _ (by rfl)
    _ = 5082 := by rw [csPC3884]; rfl

@[simp] theorem csPC3886 : Artifact.submissionArtifact.instructionPC 3853 = 5083 := by
  calc
    Artifact.submissionArtifact.instructionPC 3853 =
        Artifact.submissionArtifact.instructionPC 3852 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3852 _ (by rfl)
    _ = 5083 := by rw [csPC3885]; rfl

@[simp] theorem csPC3887 : Artifact.submissionArtifact.instructionPC 3854 = 5084 := by
  calc
    Artifact.submissionArtifact.instructionPC 3854 =
        Artifact.submissionArtifact.instructionPC 3853 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3853 _ (by rfl)
    _ = 5084 := by rw [csPC3886]; rfl

@[simp] theorem csPC3888 : Artifact.submissionArtifact.instructionPC 3855 = 5085 := by
  calc
    Artifact.submissionArtifact.instructionPC 3855 =
        Artifact.submissionArtifact.instructionPC 3854 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3854 _ (by rfl)
    _ = 5085 := by rw [csPC3887]; rfl

@[simp] theorem csPC3889 : Artifact.submissionArtifact.instructionPC 3856 = 5086 := by
  calc
    Artifact.submissionArtifact.instructionPC 3856 =
        Artifact.submissionArtifact.instructionPC 3855 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3855 _ (by rfl)
    _ = 5086 := by rw [csPC3888]; rfl

@[simp] theorem csPC3890 : Artifact.submissionArtifact.instructionPC 3857 = 5087 := by
  calc
    Artifact.submissionArtifact.instructionPC 3857 =
        Artifact.submissionArtifact.instructionPC 3856 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3856 _ (by rfl)
    _ = 5087 := by rw [csPC3889]; rfl

@[simp] theorem csPC3891 : Artifact.submissionArtifact.instructionPC 3858 = 5088 := by
  calc
    Artifact.submissionArtifact.instructionPC 3858 =
        Artifact.submissionArtifact.instructionPC 3857 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3857 _ (by rfl)
    _ = 5088 := by rw [csPC3890]; rfl

@[simp] theorem csPC3892 : Artifact.submissionArtifact.instructionPC 3859 = 5089 := by
  calc
    Artifact.submissionArtifact.instructionPC 3859 =
        Artifact.submissionArtifact.instructionPC 3858 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3858 _ (by rfl)
    _ = 5089 := by rw [csPC3891]; rfl

@[simp] theorem csPC3893 : Artifact.submissionArtifact.instructionPC 3860 = 5090 := by
  calc
    Artifact.submissionArtifact.instructionPC 3860 =
        Artifact.submissionArtifact.instructionPC 3859 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3859 _ (by rfl)
    _ = 5090 := by rw [csPC3892]; rfl

@[simp] theorem csPC3894 : Artifact.submissionArtifact.instructionPC 3861 = 5091 := by
  calc
    Artifact.submissionArtifact.instructionPC 3861 =
        Artifact.submissionArtifact.instructionPC 3860 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3860 _ (by rfl)
    _ = 5091 := by rw [csPC3893]; rfl

@[simp] theorem csPC3895 : Artifact.submissionArtifact.instructionPC 3862 = 5092 := by
  calc
    Artifact.submissionArtifact.instructionPC 3862 =
        Artifact.submissionArtifact.instructionPC 3861 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3861 _ (by rfl)
    _ = 5092 := by rw [csPC3894]; rfl

@[simp] theorem csPC3896 : Artifact.submissionArtifact.instructionPC 3863 = 5093 := by
  calc
    Artifact.submissionArtifact.instructionPC 3863 =
        Artifact.submissionArtifact.instructionPC 3862 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3862 _ (by rfl)
    _ = 5093 := by rw [csPC3895]; rfl

@[simp] theorem csPC3897 : Artifact.submissionArtifact.instructionPC 3864 = 5094 := by
  calc
    Artifact.submissionArtifact.instructionPC 3864 =
        Artifact.submissionArtifact.instructionPC 3863 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3863 _ (by rfl)
    _ = 5094 := by rw [csPC3896]; rfl

@[simp] theorem csPC3898 : Artifact.submissionArtifact.instructionPC 3865 = 5095 := by
  calc
    Artifact.submissionArtifact.instructionPC 3865 =
        Artifact.submissionArtifact.instructionPC 3864 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3864 _ (by rfl)
    _ = 5095 := by rw [csPC3897]; rfl

@[simp] theorem csPC3899 : Artifact.submissionArtifact.instructionPC 3866 = 5096 := by
  calc
    Artifact.submissionArtifact.instructionPC 3866 =
        Artifact.submissionArtifact.instructionPC 3865 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3865 _ (by rfl)
    _ = 5096 := by rw [csPC3898]; rfl

@[simp] theorem csPC3900 : Artifact.submissionArtifact.instructionPC 3867 = 5097 := by
  calc
    Artifact.submissionArtifact.instructionPC 3867 =
        Artifact.submissionArtifact.instructionPC 3866 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3866 _ (by rfl)
    _ = 5097 := by rw [csPC3899]; rfl

@[simp] theorem csPC3901 : Artifact.submissionArtifact.instructionPC 3868 = 5100 := by
  calc
    Artifact.submissionArtifact.instructionPC 3868 =
        Artifact.submissionArtifact.instructionPC 3867 +
          (YulEvmCompiler.Instr.push 2 7328).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3867 _ (by rfl)
    _ = 5100 := by rw [csPC3900]; rfl

@[simp] theorem csPC3902 : Artifact.submissionArtifact.instructionPC 3869 = 5101 := by
  calc
    Artifact.submissionArtifact.instructionPC 3869 =
        Artifact.submissionArtifact.instructionPC 3868 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3868 _ (by rfl)
    _ = 5101 := by rw [csPC3901]; rfl

@[simp] theorem csPC3903 : Artifact.submissionArtifact.instructionPC 3870 = 5104 := by
  calc
    Artifact.submissionArtifact.instructionPC 3870 =
        Artifact.submissionArtifact.instructionPC 3869 +
          (YulEvmCompiler.Instr.push 2 8384).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3869 _ (by rfl)
    _ = 5104 := by rw [csPC3902]; rfl

@[simp] theorem csPC3904 : Artifact.submissionArtifact.instructionPC 3871 = 5105 := by
  calc
    Artifact.submissionArtifact.instructionPC 3871 =
        Artifact.submissionArtifact.instructionPC 3870 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3870 _ (by rfl)
    _ = 5105 := by rw [csPC3903]; rfl

@[simp] theorem csPC3905 : Artifact.submissionArtifact.instructionPC 3872 = 5107 := by
  calc
    Artifact.submissionArtifact.instructionPC 3872 =
        Artifact.submissionArtifact.instructionPC 3871 +
          (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3871 _ (by rfl)
    _ = 5107 := by rw [csPC3904]; rfl

@[simp] theorem csPC3906 : Artifact.submissionArtifact.instructionPC 3873 = 5108 := by
  calc
    Artifact.submissionArtifact.instructionPC 3873 =
        Artifact.submissionArtifact.instructionPC 3872 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3872 _ (by rfl)
    _ = 5108 := by rw [csPC3905]; rfl

@[simp] theorem csPC3907 : Artifact.submissionArtifact.instructionPC 3874 = 5109 := by
  calc
    Artifact.submissionArtifact.instructionPC 3874 =
        Artifact.submissionArtifact.instructionPC 3873 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3873 _ (by rfl)
    _ = 5109 := by rw [csPC3906]; rfl

@[simp] theorem csPC3908 : Artifact.submissionArtifact.instructionPC 3875 = 5110 := by
  calc
    Artifact.submissionArtifact.instructionPC 3875 =
        Artifact.submissionArtifact.instructionPC 3874 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3874 _ (by rfl)
    _ = 5110 := by rw [csPC3907]; rfl

@[simp] theorem csPC3909 : Artifact.submissionArtifact.instructionPC 3876 = 5111 := by
  calc
    Artifact.submissionArtifact.instructionPC 3876 =
        Artifact.submissionArtifact.instructionPC 3875 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3875 _ (by rfl)
    _ = 5111 := by rw [csPC3908]; rfl

@[simp] theorem csPC3910 : Artifact.submissionArtifact.instructionPC 3877 = 5112 := by
  calc
    Artifact.submissionArtifact.instructionPC 3877 =
        Artifact.submissionArtifact.instructionPC 3876 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3876 _ (by rfl)
    _ = 5112 := by rw [csPC3909]; rfl

@[simp] theorem csPC3911 : Artifact.submissionArtifact.instructionPC 3878 = 5113 := by
  calc
    Artifact.submissionArtifact.instructionPC 3878 =
        Artifact.submissionArtifact.instructionPC 3877 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3877 _ (by rfl)
    _ = 5113 := by rw [csPC3910]; rfl

@[simp] theorem csPC3912 : Artifact.submissionArtifact.instructionPC 3879 = 5114 := by
  calc
    Artifact.submissionArtifact.instructionPC 3879 =
        Artifact.submissionArtifact.instructionPC 3878 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3878 _ (by rfl)
    _ = 5114 := by rw [csPC3911]; rfl

@[simp] theorem csPC3913 : Artifact.submissionArtifact.instructionPC 3880 = 5115 := by
  calc
    Artifact.submissionArtifact.instructionPC 3880 =
        Artifact.submissionArtifact.instructionPC 3879 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3879 _ (by rfl)
    _ = 5115 := by rw [csPC3912]; rfl

@[simp] theorem csPC3914 : Artifact.submissionArtifact.instructionPC 3881 = 5116 := by
  calc
    Artifact.submissionArtifact.instructionPC 3881 =
        Artifact.submissionArtifact.instructionPC 3880 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3880 _ (by rfl)
    _ = 5116 := by rw [csPC3913]; rfl

@[simp] theorem csPC3915 : Artifact.submissionArtifact.instructionPC 3882 = 5117 := by
  calc
    Artifact.submissionArtifact.instructionPC 3882 =
        Artifact.submissionArtifact.instructionPC 3881 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3881 _ (by rfl)
    _ = 5117 := by rw [csPC3914]; rfl

@[simp] theorem csPC3916 : Artifact.submissionArtifact.instructionPC 3883 = 5118 := by
  calc
    Artifact.submissionArtifact.instructionPC 3883 =
        Artifact.submissionArtifact.instructionPC 3882 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3882 _ (by rfl)
    _ = 5118 := by rw [csPC3915]; rfl

@[simp] theorem csPC3917 : Artifact.submissionArtifact.instructionPC 3884 = 5119 := by
  calc
    Artifact.submissionArtifact.instructionPC 3884 =
        Artifact.submissionArtifact.instructionPC 3883 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3883 _ (by rfl)
    _ = 5119 := by rw [csPC3916]; rfl

@[simp] theorem csPC3918 : Artifact.submissionArtifact.instructionPC 3885 = 5120 := by
  calc
    Artifact.submissionArtifact.instructionPC 3885 =
        Artifact.submissionArtifact.instructionPC 3884 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3884 _ (by rfl)
    _ = 5120 := by rw [csPC3917]; rfl

@[simp] theorem csPC3919 : Artifact.submissionArtifact.instructionPC 3886 = 5121 := by
  calc
    Artifact.submissionArtifact.instructionPC 3886 =
        Artifact.submissionArtifact.instructionPC 3885 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3885 _ (by rfl)
    _ = 5121 := by rw [csPC3918]; rfl

@[simp] theorem csPC3920 : Artifact.submissionArtifact.instructionPC 3887 = 5122 := by
  calc
    Artifact.submissionArtifact.instructionPC 3887 =
        Artifact.submissionArtifact.instructionPC 3886 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3886 _ (by rfl)
    _ = 5122 := by rw [csPC3919]; rfl

@[simp] theorem csPC3921 : Artifact.submissionArtifact.instructionPC 3888 = 5123 := by
  calc
    Artifact.submissionArtifact.instructionPC 3888 =
        Artifact.submissionArtifact.instructionPC 3887 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3887 _ (by rfl)
    _ = 5123 := by rw [csPC3920]; rfl

@[simp] theorem csPC3922 : Artifact.submissionArtifact.instructionPC 3889 = 5124 := by
  calc
    Artifact.submissionArtifact.instructionPC 3889 =
        Artifact.submissionArtifact.instructionPC 3888 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3888 _ (by rfl)
    _ = 5124 := by rw [csPC3921]; rfl

@[simp] theorem csPC3923 : Artifact.submissionArtifact.instructionPC 3890 = 5127 := by
  calc
    Artifact.submissionArtifact.instructionPC 3890 =
        Artifact.submissionArtifact.instructionPC 3889 +
          (YulEvmCompiler.Instr.push 2 7296).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3889 _ (by rfl)
    _ = 5127 := by rw [csPC3922]; rfl

@[simp] theorem csPC3924 : Artifact.submissionArtifact.instructionPC 3891 = 5128 := by
  calc
    Artifact.submissionArtifact.instructionPC 3891 =
        Artifact.submissionArtifact.instructionPC 3890 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3890 _ (by rfl)
    _ = 5128 := by rw [csPC3923]; rfl

@[simp] theorem csJump5131 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5128 = true := by
  simpa only [Artifact.instructionPC, csPC3924] using Artifact.isValidJumpDest_index 3891 (by rfl)

@[simp] theorem csPC3925 : Artifact.submissionArtifact.instructionPC 3892 = 5129 := by
  calc
    Artifact.submissionArtifact.instructionPC 3892 =
        Artifact.submissionArtifact.instructionPC 3891 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3891 _ (by rfl)
    _ = 5129 := by rw [csPC3924]; rfl

@[simp] theorem csPC3926 : Artifact.submissionArtifact.instructionPC 3893 = 5132 := by
  calc
    Artifact.submissionArtifact.instructionPC 3893 =
        Artifact.submissionArtifact.instructionPC 3892 +
          (YulEvmCompiler.Instr.push 2 8352).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3892 _ (by rfl)
    _ = 5132 := by rw [csPC3925]; rfl

@[simp] theorem csPC3927 : Artifact.submissionArtifact.instructionPC 3894 = 5133 := by
  calc
    Artifact.submissionArtifact.instructionPC 3894 =
        Artifact.submissionArtifact.instructionPC 3893 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3893 _ (by rfl)
    _ = 5133 := by rw [csPC3926]; rfl

@[simp] theorem csPC3928 : Artifact.submissionArtifact.instructionPC 3895 = 5135 := by
  calc
    Artifact.submissionArtifact.instructionPC 3895 =
        Artifact.submissionArtifact.instructionPC 3894 +
          (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3894 _ (by rfl)
    _ = 5135 := by rw [csPC3927]; rfl

@[simp] theorem csPC3929 : Artifact.submissionArtifact.instructionPC 3896 = 5136 := by
  calc
    Artifact.submissionArtifact.instructionPC 3896 =
        Artifact.submissionArtifact.instructionPC 3895 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3895 _ (by rfl)
    _ = 5136 := by rw [csPC3928]; rfl

@[simp] theorem csPC3930 : Artifact.submissionArtifact.instructionPC 3897 = 5137 := by
  calc
    Artifact.submissionArtifact.instructionPC 3897 =
        Artifact.submissionArtifact.instructionPC 3896 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3896 _ (by rfl)
    _ = 5137 := by rw [csPC3929]; rfl

@[simp] theorem csPC3931 : Artifact.submissionArtifact.instructionPC 3898 = 5138 := by
  calc
    Artifact.submissionArtifact.instructionPC 3898 =
        Artifact.submissionArtifact.instructionPC 3897 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3897 _ (by rfl)
    _ = 5138 := by rw [csPC3930]; rfl

@[simp] theorem csPC3932 : Artifact.submissionArtifact.instructionPC 3899 = 5139 := by
  calc
    Artifact.submissionArtifact.instructionPC 3899 =
        Artifact.submissionArtifact.instructionPC 3898 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3898 _ (by rfl)
    _ = 5139 := by rw [csPC3931]; rfl

@[simp] theorem csPC3933 : Artifact.submissionArtifact.instructionPC 3900 = 5140 := by
  calc
    Artifact.submissionArtifact.instructionPC 3900 =
        Artifact.submissionArtifact.instructionPC 3899 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3899 _ (by rfl)
    _ = 5140 := by rw [csPC3932]; rfl

@[simp] theorem csPC3934 : Artifact.submissionArtifact.instructionPC 3901 = 5141 := by
  calc
    Artifact.submissionArtifact.instructionPC 3901 =
        Artifact.submissionArtifact.instructionPC 3900 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3900 _ (by rfl)
    _ = 5141 := by rw [csPC3933]; rfl

@[simp] theorem csPC3935 : Artifact.submissionArtifact.instructionPC 3902 = 5142 := by
  calc
    Artifact.submissionArtifact.instructionPC 3902 =
        Artifact.submissionArtifact.instructionPC 3901 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3901 _ (by rfl)
    _ = 5142 := by rw [csPC3934]; rfl

@[simp] theorem csPC3936 : Artifact.submissionArtifact.instructionPC 3903 = 5143 := by
  calc
    Artifact.submissionArtifact.instructionPC 3903 =
        Artifact.submissionArtifact.instructionPC 3902 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3902 _ (by rfl)
    _ = 5143 := by rw [csPC3935]; rfl

@[simp] theorem csPC3937 : Artifact.submissionArtifact.instructionPC 3904 = 5144 := by
  calc
    Artifact.submissionArtifact.instructionPC 3904 =
        Artifact.submissionArtifact.instructionPC 3903 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3903 _ (by rfl)
    _ = 5144 := by rw [csPC3936]; rfl

@[simp] theorem csPC3938 : Artifact.submissionArtifact.instructionPC 3905 = 5145 := by
  calc
    Artifact.submissionArtifact.instructionPC 3905 =
        Artifact.submissionArtifact.instructionPC 3904 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3904 _ (by rfl)
    _ = 5145 := by rw [csPC3937]; rfl

@[simp] theorem csPC3939 : Artifact.submissionArtifact.instructionPC 3906 = 5146 := by
  calc
    Artifact.submissionArtifact.instructionPC 3906 =
        Artifact.submissionArtifact.instructionPC 3905 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3905 _ (by rfl)
    _ = 5146 := by rw [csPC3938]; rfl

@[simp] theorem csPC3940 : Artifact.submissionArtifact.instructionPC 3907 = 5147 := by
  calc
    Artifact.submissionArtifact.instructionPC 3907 =
        Artifact.submissionArtifact.instructionPC 3906 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3906 _ (by rfl)
    _ = 5147 := by rw [csPC3939]; rfl

@[simp] theorem csPC3941 : Artifact.submissionArtifact.instructionPC 3908 = 5148 := by
  calc
    Artifact.submissionArtifact.instructionPC 3908 =
        Artifact.submissionArtifact.instructionPC 3907 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3907 _ (by rfl)
    _ = 5148 := by rw [csPC3940]; rfl

@[simp] theorem csPC3942 : Artifact.submissionArtifact.instructionPC 3909 = 5149 := by
  calc
    Artifact.submissionArtifact.instructionPC 3909 =
        Artifact.submissionArtifact.instructionPC 3908 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3908 _ (by rfl)
    _ = 5149 := by rw [csPC3941]; rfl

@[simp] theorem csPC3943 : Artifact.submissionArtifact.instructionPC 3910 = 5150 := by
  calc
    Artifact.submissionArtifact.instructionPC 3910 =
        Artifact.submissionArtifact.instructionPC 3909 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3909 _ (by rfl)
    _ = 5150 := by rw [csPC3942]; rfl

@[simp] theorem csPC3944 : Artifact.submissionArtifact.instructionPC 3911 = 5151 := by
  calc
    Artifact.submissionArtifact.instructionPC 3911 =
        Artifact.submissionArtifact.instructionPC 3910 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3910 _ (by rfl)
    _ = 5151 := by rw [csPC3943]; rfl

@[simp] theorem csPC3945 : Artifact.submissionArtifact.instructionPC 3912 = 5152 := by
  calc
    Artifact.submissionArtifact.instructionPC 3912 =
        Artifact.submissionArtifact.instructionPC 3911 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3911 _ (by rfl)
    _ = 5152 := by rw [csPC3944]; rfl

@[simp] theorem csPC3946 : Artifact.submissionArtifact.instructionPC 3913 = 5155 := by
  calc
    Artifact.submissionArtifact.instructionPC 3913 =
        Artifact.submissionArtifact.instructionPC 3912 +
          (YulEvmCompiler.Instr.push 2 7264).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3912 _ (by rfl)
    _ = 5155 := by rw [csPC3945]; rfl

@[simp] theorem csPC3947 : Artifact.submissionArtifact.instructionPC 3914 = 5156 := by
  calc
    Artifact.submissionArtifact.instructionPC 3914 =
        Artifact.submissionArtifact.instructionPC 3913 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3913 _ (by rfl)
    _ = 5156 := by rw [csPC3946]; rfl

@[simp] theorem csPC3948 : Artifact.submissionArtifact.instructionPC 3915 = 5159 := by
  calc
    Artifact.submissionArtifact.instructionPC 3915 =
        Artifact.submissionArtifact.instructionPC 3914 +
          (YulEvmCompiler.Instr.push 2 8320).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3914 _ (by rfl)
    _ = 5159 := by rw [csPC3947]; rfl

@[simp] theorem csPC3949 : Artifact.submissionArtifact.instructionPC 3916 = 5160 := by
  calc
    Artifact.submissionArtifact.instructionPC 3916 =
        Artifact.submissionArtifact.instructionPC 3915 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3915 _ (by rfl)
    _ = 5160 := by rw [csPC3948]; rfl

@[simp] theorem csPC3950 : Artifact.submissionArtifact.instructionPC 3917 = 5162 := by
  calc
    Artifact.submissionArtifact.instructionPC 3917 =
        Artifact.submissionArtifact.instructionPC 3916 +
          (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3916 _ (by rfl)
    _ = 5162 := by rw [csPC3949]; rfl

@[simp] theorem csPC3951 : Artifact.submissionArtifact.instructionPC 3918 = 5163 := by
  calc
    Artifact.submissionArtifact.instructionPC 3918 =
        Artifact.submissionArtifact.instructionPC 3917 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3917 _ (by rfl)
    _ = 5163 := by rw [csPC3950]; rfl

@[simp] theorem csPC3952 : Artifact.submissionArtifact.instructionPC 3919 = 5164 := by
  calc
    Artifact.submissionArtifact.instructionPC 3919 =
        Artifact.submissionArtifact.instructionPC 3918 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3918 _ (by rfl)
    _ = 5164 := by rw [csPC3951]; rfl

@[simp] theorem csPC3953 : Artifact.submissionArtifact.instructionPC 3920 = 5165 := by
  calc
    Artifact.submissionArtifact.instructionPC 3920 =
        Artifact.submissionArtifact.instructionPC 3919 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3919 _ (by rfl)
    _ = 5165 := by rw [csPC3952]; rfl

@[simp] theorem csPC3954 : Artifact.submissionArtifact.instructionPC 3921 = 5166 := by
  calc
    Artifact.submissionArtifact.instructionPC 3921 =
        Artifact.submissionArtifact.instructionPC 3920 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3920 _ (by rfl)
    _ = 5166 := by rw [csPC3953]; rfl

@[simp] theorem csPC3955 : Artifact.submissionArtifact.instructionPC 3922 = 5167 := by
  calc
    Artifact.submissionArtifact.instructionPC 3922 =
        Artifact.submissionArtifact.instructionPC 3921 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3921 _ (by rfl)
    _ = 5167 := by rw [csPC3954]; rfl

@[simp] theorem csPC3956 : Artifact.submissionArtifact.instructionPC 3923 = 5168 := by
  calc
    Artifact.submissionArtifact.instructionPC 3923 =
        Artifact.submissionArtifact.instructionPC 3922 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3922 _ (by rfl)
    _ = 5168 := by rw [csPC3955]; rfl

@[simp] theorem csPC3957 : Artifact.submissionArtifact.instructionPC 3924 = 5169 := by
  calc
    Artifact.submissionArtifact.instructionPC 3924 =
        Artifact.submissionArtifact.instructionPC 3923 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3923 _ (by rfl)
    _ = 5169 := by rw [csPC3956]; rfl

@[simp] theorem csPC3958 : Artifact.submissionArtifact.instructionPC 3925 = 5170 := by
  calc
    Artifact.submissionArtifact.instructionPC 3925 =
        Artifact.submissionArtifact.instructionPC 3924 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3924 _ (by rfl)
    _ = 5170 := by rw [csPC3957]; rfl

@[simp] theorem csPC3959 : Artifact.submissionArtifact.instructionPC 3926 = 5171 := by
  calc
    Artifact.submissionArtifact.instructionPC 3926 =
        Artifact.submissionArtifact.instructionPC 3925 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3925 _ (by rfl)
    _ = 5171 := by rw [csPC3958]; rfl

@[simp] theorem csPC3960 : Artifact.submissionArtifact.instructionPC 3927 = 5172 := by
  calc
    Artifact.submissionArtifact.instructionPC 3927 =
        Artifact.submissionArtifact.instructionPC 3926 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3926 _ (by rfl)
    _ = 5172 := by rw [csPC3959]; rfl

@[simp] theorem csPC3961 : Artifact.submissionArtifact.instructionPC 3928 = 5173 := by
  calc
    Artifact.submissionArtifact.instructionPC 3928 =
        Artifact.submissionArtifact.instructionPC 3927 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3927 _ (by rfl)
    _ = 5173 := by rw [csPC3960]; rfl

@[simp] theorem csPC3962 : Artifact.submissionArtifact.instructionPC 3929 = 5174 := by
  calc
    Artifact.submissionArtifact.instructionPC 3929 =
        Artifact.submissionArtifact.instructionPC 3928 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3928 _ (by rfl)
    _ = 5174 := by rw [csPC3961]; rfl

@[simp] theorem csPC3963 : Artifact.submissionArtifact.instructionPC 3930 = 5175 := by
  calc
    Artifact.submissionArtifact.instructionPC 3930 =
        Artifact.submissionArtifact.instructionPC 3929 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3929 _ (by rfl)
    _ = 5175 := by rw [csPC3962]; rfl

@[simp] theorem csPC3964 : Artifact.submissionArtifact.instructionPC 3931 = 5176 := by
  calc
    Artifact.submissionArtifact.instructionPC 3931 =
        Artifact.submissionArtifact.instructionPC 3930 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3930 _ (by rfl)
    _ = 5176 := by rw [csPC3963]; rfl

@[simp] theorem csPC3965 : Artifact.submissionArtifact.instructionPC 3932 = 5177 := by
  calc
    Artifact.submissionArtifact.instructionPC 3932 =
        Artifact.submissionArtifact.instructionPC 3931 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3931 _ (by rfl)
    _ = 5177 := by rw [csPC3964]; rfl

@[simp] theorem csPC3966 : Artifact.submissionArtifact.instructionPC 3933 = 5178 := by
  calc
    Artifact.submissionArtifact.instructionPC 3933 =
        Artifact.submissionArtifact.instructionPC 3932 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3932 _ (by rfl)
    _ = 5178 := by rw [csPC3965]; rfl

@[simp] theorem csPC3967 : Artifact.submissionArtifact.instructionPC 3934 = 5179 := by
  calc
    Artifact.submissionArtifact.instructionPC 3934 =
        Artifact.submissionArtifact.instructionPC 3933 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3933 _ (by rfl)
    _ = 5179 := by rw [csPC3966]; rfl

@[simp] theorem csPC3968 : Artifact.submissionArtifact.instructionPC 3935 = 5182 := by
  calc
    Artifact.submissionArtifact.instructionPC 3935 =
        Artifact.submissionArtifact.instructionPC 3934 +
          (YulEvmCompiler.Instr.push 2 7232).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3934 _ (by rfl)
    _ = 5182 := by rw [csPC3967]; rfl

@[simp] theorem csPC3969 : Artifact.submissionArtifact.instructionPC 3936 = 5183 := by
  calc
    Artifact.submissionArtifact.instructionPC 3936 =
        Artifact.submissionArtifact.instructionPC 3935 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3935 _ (by rfl)
    _ = 5183 := by rw [csPC3968]; rfl

@[simp] theorem csPC3970 : Artifact.submissionArtifact.instructionPC 3937 = 5186 := by
  calc
    Artifact.submissionArtifact.instructionPC 3937 =
        Artifact.submissionArtifact.instructionPC 3936 +
          (YulEvmCompiler.Instr.push 2 8288).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3936 _ (by rfl)
    _ = 5186 := by rw [csPC3969]; rfl

@[simp] theorem csPC3971 : Artifact.submissionArtifact.instructionPC 3938 = 5187 := by
  calc
    Artifact.submissionArtifact.instructionPC 3938 =
        Artifact.submissionArtifact.instructionPC 3937 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3937 _ (by rfl)
    _ = 5187 := by rw [csPC3970]; rfl

@[simp] theorem csPC3972 : Artifact.submissionArtifact.instructionPC 3939 = 5189 := by
  calc
    Artifact.submissionArtifact.instructionPC 3939 =
        Artifact.submissionArtifact.instructionPC 3938 +
          (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3938 _ (by rfl)
    _ = 5189 := by rw [csPC3971]; rfl

@[simp] theorem csPC3973 : Artifact.submissionArtifact.instructionPC 3940 = 5190 := by
  calc
    Artifact.submissionArtifact.instructionPC 3940 =
        Artifact.submissionArtifact.instructionPC 3939 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3939 _ (by rfl)
    _ = 5190 := by rw [csPC3972]; rfl

@[simp] theorem csPC3974 : Artifact.submissionArtifact.instructionPC 3941 = 5191 := by
  calc
    Artifact.submissionArtifact.instructionPC 3941 =
        Artifact.submissionArtifact.instructionPC 3940 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3940 _ (by rfl)
    _ = 5191 := by rw [csPC3973]; rfl

@[simp] theorem csPC3975 : Artifact.submissionArtifact.instructionPC 3942 = 5192 := by
  calc
    Artifact.submissionArtifact.instructionPC 3942 =
        Artifact.submissionArtifact.instructionPC 3941 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3941 _ (by rfl)
    _ = 5192 := by rw [csPC3974]; rfl

@[simp] theorem csPC3976 : Artifact.submissionArtifact.instructionPC 3943 = 5193 := by
  calc
    Artifact.submissionArtifact.instructionPC 3943 =
        Artifact.submissionArtifact.instructionPC 3942 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3942 _ (by rfl)
    _ = 5193 := by rw [csPC3975]; rfl

@[simp] theorem csPC3977 : Artifact.submissionArtifact.instructionPC 3944 = 5194 := by
  calc
    Artifact.submissionArtifact.instructionPC 3944 =
        Artifact.submissionArtifact.instructionPC 3943 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3943 _ (by rfl)
    _ = 5194 := by rw [csPC3976]; rfl

@[simp] theorem csPC3978 : Artifact.submissionArtifact.instructionPC 3945 = 5195 := by
  calc
    Artifact.submissionArtifact.instructionPC 3945 =
        Artifact.submissionArtifact.instructionPC 3944 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3944 _ (by rfl)
    _ = 5195 := by rw [csPC3977]; rfl

@[simp] theorem csPC3979 : Artifact.submissionArtifact.instructionPC 3946 = 5196 := by
  calc
    Artifact.submissionArtifact.instructionPC 3946 =
        Artifact.submissionArtifact.instructionPC 3945 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3945 _ (by rfl)
    _ = 5196 := by rw [csPC3978]; rfl

@[simp] theorem csPC3980 : Artifact.submissionArtifact.instructionPC 3947 = 5197 := by
  calc
    Artifact.submissionArtifact.instructionPC 3947 =
        Artifact.submissionArtifact.instructionPC 3946 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3946 _ (by rfl)
    _ = 5197 := by rw [csPC3979]; rfl

@[simp] theorem csPC3981 : Artifact.submissionArtifact.instructionPC 3948 = 5198 := by
  calc
    Artifact.submissionArtifact.instructionPC 3948 =
        Artifact.submissionArtifact.instructionPC 3947 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3947 _ (by rfl)
    _ = 5198 := by rw [csPC3980]; rfl

@[simp] theorem csPC3982 : Artifact.submissionArtifact.instructionPC 3949 = 5199 := by
  calc
    Artifact.submissionArtifact.instructionPC 3949 =
        Artifact.submissionArtifact.instructionPC 3948 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3948 _ (by rfl)
    _ = 5199 := by rw [csPC3981]; rfl

@[simp] theorem csPC3983 : Artifact.submissionArtifact.instructionPC 3950 = 5200 := by
  calc
    Artifact.submissionArtifact.instructionPC 3950 =
        Artifact.submissionArtifact.instructionPC 3949 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3949 _ (by rfl)
    _ = 5200 := by rw [csPC3982]; rfl

@[simp] theorem csPC3984 : Artifact.submissionArtifact.instructionPC 3951 = 5201 := by
  calc
    Artifact.submissionArtifact.instructionPC 3951 =
        Artifact.submissionArtifact.instructionPC 3950 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3950 _ (by rfl)
    _ = 5201 := by rw [csPC3983]; rfl

@[simp] theorem csPC3985 : Artifact.submissionArtifact.instructionPC 3952 = 5202 := by
  calc
    Artifact.submissionArtifact.instructionPC 3952 =
        Artifact.submissionArtifact.instructionPC 3951 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3951 _ (by rfl)
    _ = 5202 := by rw [csPC3984]; rfl

@[simp] theorem csPC3986 : Artifact.submissionArtifact.instructionPC 3953 = 5203 := by
  calc
    Artifact.submissionArtifact.instructionPC 3953 =
        Artifact.submissionArtifact.instructionPC 3952 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3952 _ (by rfl)
    _ = 5203 := by rw [csPC3985]; rfl

@[simp] theorem csPC3987 : Artifact.submissionArtifact.instructionPC 3954 = 5204 := by
  calc
    Artifact.submissionArtifact.instructionPC 3954 =
        Artifact.submissionArtifact.instructionPC 3953 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3953 _ (by rfl)
    _ = 5204 := by rw [csPC3986]; rfl

@[simp] theorem csPC3988 : Artifact.submissionArtifact.instructionPC 3955 = 5205 := by
  calc
    Artifact.submissionArtifact.instructionPC 3955 =
        Artifact.submissionArtifact.instructionPC 3954 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3954 _ (by rfl)
    _ = 5205 := by rw [csPC3987]; rfl

@[simp] theorem csPC3989 : Artifact.submissionArtifact.instructionPC 3956 = 5206 := by
  calc
    Artifact.submissionArtifact.instructionPC 3956 =
        Artifact.submissionArtifact.instructionPC 3955 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3955 _ (by rfl)
    _ = 5206 := by rw [csPC3988]; rfl

@[simp] theorem csPC3990 : Artifact.submissionArtifact.instructionPC 3957 = 5209 := by
  calc
    Artifact.submissionArtifact.instructionPC 3957 =
        Artifact.submissionArtifact.instructionPC 3956 +
          (YulEvmCompiler.Instr.push 2 7200).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3956 _ (by rfl)
    _ = 5209 := by rw [csPC3989]; rfl

@[simp] theorem csPC3991 : Artifact.submissionArtifact.instructionPC 3958 = 5210 := by
  calc
    Artifact.submissionArtifact.instructionPC 3958 =
        Artifact.submissionArtifact.instructionPC 3957 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3957 _ (by rfl)
    _ = 5210 := by rw [csPC3990]; rfl

@[simp] theorem csPC3992 : Artifact.submissionArtifact.instructionPC 3959 = 5213 := by
  calc
    Artifact.submissionArtifact.instructionPC 3959 =
        Artifact.submissionArtifact.instructionPC 3958 +
          (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3958 _ (by rfl)
    _ = 5213 := by rw [csPC3991]; rfl

@[simp] theorem csPC3993 : Artifact.submissionArtifact.instructionPC 3960 = 5214 := by
  calc
    Artifact.submissionArtifact.instructionPC 3960 =
        Artifact.submissionArtifact.instructionPC 3959 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3959 _ (by rfl)
    _ = 5214 := by rw [csPC3992]; rfl

@[simp] theorem csPC3994 : Artifact.submissionArtifact.instructionPC 3961 = 5215 := by
  calc
    Artifact.submissionArtifact.instructionPC 3961 =
        Artifact.submissionArtifact.instructionPC 3960 +
          (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3960 _ (by rfl)
    _ = 5215 := by rw [csPC3993]; rfl

@[simp] theorem csPC3995 : Artifact.submissionArtifact.instructionPC 3962 = 5216 := by
  calc
    Artifact.submissionArtifact.instructionPC 3962 =
        Artifact.submissionArtifact.instructionPC 3961 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3961 _ (by rfl)
    _ = 5216 := by rw [csPC3994]; rfl

@[simp] theorem csPC3996 : Artifact.submissionArtifact.instructionPC 3963 = 5217 := by
  calc
    Artifact.submissionArtifact.instructionPC 3963 =
        Artifact.submissionArtifact.instructionPC 3962 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3962 _ (by rfl)
    _ = 5217 := by rw [csPC3995]; rfl

@[simp] theorem csPC3997 : Artifact.submissionArtifact.instructionPC 3964 = 5218 := by
  calc
    Artifact.submissionArtifact.instructionPC 3964 =
        Artifact.submissionArtifact.instructionPC 3963 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3963 _ (by rfl)
    _ = 5218 := by rw [csPC3996]; rfl

@[simp] theorem csPC3998 : Artifact.submissionArtifact.instructionPC 3965 = 5219 := by
  calc
    Artifact.submissionArtifact.instructionPC 3965 =
        Artifact.submissionArtifact.instructionPC 3964 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3964 _ (by rfl)
    _ = 5219 := by rw [csPC3997]; rfl

@[simp] theorem csPC3999 : Artifact.submissionArtifact.instructionPC 3966 = 5220 := by
  calc
    Artifact.submissionArtifact.instructionPC 3966 =
        Artifact.submissionArtifact.instructionPC 3965 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3965 _ (by rfl)
    _ = 5220 := by rw [csPC3998]; rfl

@[simp] theorem csPC4000 : Artifact.submissionArtifact.instructionPC 3967 = 5221 := by
  calc
    Artifact.submissionArtifact.instructionPC 3967 =
        Artifact.submissionArtifact.instructionPC 3966 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3966 _ (by rfl)
    _ = 5221 := by rw [csPC3999]; rfl

@[simp] theorem csPC4001 : Artifact.submissionArtifact.instructionPC 3968 = 5222 := by
  calc
    Artifact.submissionArtifact.instructionPC 3968 =
        Artifact.submissionArtifact.instructionPC 3967 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3967 _ (by rfl)
    _ = 5222 := by rw [csPC4000]; rfl

@[simp] theorem csPC4002 : Artifact.submissionArtifact.instructionPC 3969 = 5223 := by
  calc
    Artifact.submissionArtifact.instructionPC 3969 =
        Artifact.submissionArtifact.instructionPC 3968 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3968 _ (by rfl)
    _ = 5223 := by rw [csPC4001]; rfl

@[simp] theorem csPC4003 : Artifact.submissionArtifact.instructionPC 3970 = 5224 := by
  calc
    Artifact.submissionArtifact.instructionPC 3970 =
        Artifact.submissionArtifact.instructionPC 3969 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3969 _ (by rfl)
    _ = 5224 := by rw [csPC4002]; rfl

@[simp] theorem csPC4004 : Artifact.submissionArtifact.instructionPC 3971 = 5225 := by
  calc
    Artifact.submissionArtifact.instructionPC 3971 =
        Artifact.submissionArtifact.instructionPC 3970 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3970 _ (by rfl)
    _ = 5225 := by rw [csPC4003]; rfl

@[simp] theorem csPC4005 : Artifact.submissionArtifact.instructionPC 3972 = 5226 := by
  calc
    Artifact.submissionArtifact.instructionPC 3972 =
        Artifact.submissionArtifact.instructionPC 3971 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3971 _ (by rfl)
    _ = 5226 := by rw [csPC4004]; rfl

@[simp] theorem csPC4006 : Artifact.submissionArtifact.instructionPC 3973 = 5227 := by
  calc
    Artifact.submissionArtifact.instructionPC 3973 =
        Artifact.submissionArtifact.instructionPC 3972 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3972 _ (by rfl)
    _ = 5227 := by rw [csPC4005]; rfl

@[simp] theorem csPC4007 : Artifact.submissionArtifact.instructionPC 3974 = 5228 := by
  calc
    Artifact.submissionArtifact.instructionPC 3974 =
        Artifact.submissionArtifact.instructionPC 3973 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3973 _ (by rfl)
    _ = 5228 := by rw [csPC4006]; rfl

@[simp] theorem csPC4008 : Artifact.submissionArtifact.instructionPC 3975 = 5229 := by
  calc
    Artifact.submissionArtifact.instructionPC 3975 =
        Artifact.submissionArtifact.instructionPC 3974 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3974 _ (by rfl)
    _ = 5229 := by rw [csPC4007]; rfl

@[simp] theorem csPC4009 : Artifact.submissionArtifact.instructionPC 3976 = 5230 := by
  calc
    Artifact.submissionArtifact.instructionPC 3976 =
        Artifact.submissionArtifact.instructionPC 3975 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3975 _ (by rfl)
    _ = 5230 := by rw [csPC4008]; rfl

@[simp] theorem csPC4010 : Artifact.submissionArtifact.instructionPC 3977 = 5231 := by
  calc
    Artifact.submissionArtifact.instructionPC 3977 =
        Artifact.submissionArtifact.instructionPC 3976 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3976 _ (by rfl)
    _ = 5231 := by rw [csPC4009]; rfl

@[simp] theorem csPC4011 : Artifact.submissionArtifact.instructionPC 3978 = 5232 := by
  calc
    Artifact.submissionArtifact.instructionPC 3978 =
        Artifact.submissionArtifact.instructionPC 3977 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3977 _ (by rfl)
    _ = 5232 := by rw [csPC4010]; rfl

@[simp] theorem csPC4012 : Artifact.submissionArtifact.instructionPC 3979 = 5235 := by
  calc
    Artifact.submissionArtifact.instructionPC 3979 =
        Artifact.submissionArtifact.instructionPC 3978 +
          (YulEvmCompiler.Instr.push 2 7168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3978 _ (by rfl)
    _ = 5235 := by rw [csPC4011]; rfl

@[simp] theorem csPC4013 : Artifact.submissionArtifact.instructionPC 3980 = 5236 := by
  calc
    Artifact.submissionArtifact.instructionPC 3980 =
        Artifact.submissionArtifact.instructionPC 3979 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3979 _ (by rfl)
    _ = 5236 := by rw [csPC4012]; rfl

@[simp] theorem csPC4014 : Artifact.submissionArtifact.instructionPC 3981 = 5237 := by
  calc
    Artifact.submissionArtifact.instructionPC 3981 =
        Artifact.submissionArtifact.instructionPC 3980 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3980 _ (by rfl)
    _ = 5237 := by rw [csPC4013]; rfl

@[simp] theorem csPC4015 : Artifact.submissionArtifact.instructionPC 3982 = 5240 := by
  calc
    Artifact.submissionArtifact.instructionPC 3982 =
        Artifact.submissionArtifact.instructionPC 3981 +
          (YulEvmCompiler.Instr.push 2 8224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3981 _ (by rfl)
    _ = 5240 := by rw [csPC4014]; rfl

@[simp] theorem csPC4016 : Artifact.submissionArtifact.instructionPC 3983 = 5241 := by
  calc
    Artifact.submissionArtifact.instructionPC 3983 =
        Artifact.submissionArtifact.instructionPC 3982 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3982 _ (by rfl)
    _ = 5241 := by rw [csPC4015]; rfl

@[simp] theorem csPC4017 : Artifact.submissionArtifact.instructionPC 3984 = 5242 := by
  calc
    Artifact.submissionArtifact.instructionPC 3984 =
        Artifact.submissionArtifact.instructionPC 3983 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3983 _ (by rfl)
    _ = 5242 := by rw [csPC4016]; rfl

@[simp] theorem csPC4018 : Artifact.submissionArtifact.instructionPC 3985 = 5245 := by
  calc
    Artifact.submissionArtifact.instructionPC 3985 =
        Artifact.submissionArtifact.instructionPC 3984 +
          (YulEvmCompiler.Instr.push 2 1087).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3984 _ (by rfl)
    _ = 5245 := by rw [csPC4017]; rfl

@[simp] theorem csPC4019 : Artifact.submissionArtifact.instructionPC 3986 = 5246 := by
  calc
    Artifact.submissionArtifact.instructionPC 3986 =
        Artifact.submissionArtifact.instructionPC 3985 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3985 _ (by rfl)
    _ = 5246 := by rw [csPC4018]; rfl

@[simp] theorem csPC4020 : Artifact.submissionArtifact.instructionPC 3987 = 5247 := by
  calc
    Artifact.submissionArtifact.instructionPC 3987 =
        Artifact.submissionArtifact.instructionPC 3986 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3986 _ (by rfl)
    _ = 5247 := by rw [csPC4019]; rfl

@[simp] theorem csPC4021 : Artifact.submissionArtifact.instructionPC 3988 = 5250 := by
  calc
    Artifact.submissionArtifact.instructionPC 3988 =
        Artifact.submissionArtifact.instructionPC 3987 +
          (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3987 _ (by rfl)
    _ = 5250 := by rw [csPC4020]; rfl

@[simp] theorem csPC4022 : Artifact.submissionArtifact.instructionPC 3989 = 5251 := by
  calc
    Artifact.submissionArtifact.instructionPC 3989 =
        Artifact.submissionArtifact.instructionPC 3988 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3988 _ (by rfl)
    _ = 5251 := by rw [csPC4021]; rfl

@[simp] theorem csPC4023 : Artifact.submissionArtifact.instructionPC 3990 = 5254 := by
  calc
    Artifact.submissionArtifact.instructionPC 3990 =
        Artifact.submissionArtifact.instructionPC 3989 +
          (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3989 _ (by rfl)
    _ = 5254 := by rw [csPC4022]; rfl

@[simp] theorem csPC4024 : Artifact.submissionArtifact.instructionPC 3991 = 5255 := by
  calc
    Artifact.submissionArtifact.instructionPC 3991 =
        Artifact.submissionArtifact.instructionPC 3990 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3990 _ (by rfl)
    _ = 5255 := by rw [csPC4023]; rfl

@[simp] theorem csPC4025 : Artifact.submissionArtifact.instructionPC 3992 = 5256 := by
  calc
    Artifact.submissionArtifact.instructionPC 3992 =
        Artifact.submissionArtifact.instructionPC 3991 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3991 _ (by rfl)
    _ = 5256 := by rw [csPC4024]; rfl

@[simp] theorem csPC4026 : Artifact.submissionArtifact.instructionPC 3993 = 5257 := by
  calc
    Artifact.submissionArtifact.instructionPC 3993 =
        Artifact.submissionArtifact.instructionPC 3992 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3992 _ (by rfl)
    _ = 5257 := by rw [csPC4025]; rfl

end Challenge.Modexp.Submission.Proofs.Fast
