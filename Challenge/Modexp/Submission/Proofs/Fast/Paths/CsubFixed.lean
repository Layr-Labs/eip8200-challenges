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
  [opAt 3790 .JUMPDEST,
   pushAt 3791 2 5248,
   opAt 3792 .MLOAD,
   pushAt 3793 2 256,
   opAt 3794 .EQ,
   pushAt 3795 2 5044,
   opAt 3796 .JUMPI,
   pushAt 3797 2 5248,
   opAt 3798 .MLOAD,
   pushAt 3799 1 128,
   opAt 3800 .EQ,
   pushAt 3801 2 4846,
   opAt 3802 .JUMPI,
   pushAt 3803 2 5344,
   opAt 3804 .MLOAD,
   pushAt 3805 2 5312,
   opAt 3806 .MLOAD,
   opAt 3807 (.Dup ⟨0, by decide⟩),
   pushAt 3808 2 3072,
   opAt 3809 .ADD,
   pushAt 3810 2 4160,
   opAt 3811 .POP,
   opAt 3812 (.Swap ⟨0, by decide⟩),
   pushAt 3813 0 0,
   opAt 3814 (.Swap ⟨2, by decide⟩),
   pushAt 3815 2 2120,
   opAt 3816 .JUMP]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3790 .JUMPDEST,
   pushAt 3791 2 5248,
   opAt 3792 .MLOAD,
   pushAt 3793 2 256,
   opAt 3794 .EQ,
   pushAt 3795 2 5044,
   opAt 3796 .JUMPI,
   opAt 3817 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3790 .JUMPDEST,
   pushAt 3791 2 5248,
   opAt 3792 .MLOAD,
   pushAt 3793 2 256,
   opAt 3794 .EQ,
   pushAt 3795 2 5044,
   opAt 3796 .JUMPI,
   pushAt 3797 2 5248,
   opAt 3798 .MLOAD,
   pushAt 3799 1 128,
   opAt 3800 .EQ,
   pushAt 3801 2 4846,
   opAt 3802 .JUMPI,
   opAt 3676 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3818 2 4384,
   opAt 3819 .MLOAD,
   pushAt 3820 1 224,
   opAt 3821 .MLOAD,
   opAt 3822 (.Dup ⟨1, by decide⟩),
   opAt 3823 (.Dup ⟨1, by decide⟩),
   opAt 3824 .GT,
   opAt 3825 (.Swap ⟨1, by decide⟩),
   opAt 3826 .SUB,
   pushAt 3827 2 3296,
   opAt 3828 .MSTORE]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3829 2 4352,
   opAt 3830 .MLOAD,
   pushAt 3831 1 192,
   opAt 3832 .MLOAD,
   opAt 3833 (.Dup ⟨1, by decide⟩),
   opAt 3834 (.Dup ⟨1, by decide⟩),
   opAt 3835 .GT,
   opAt 3836 (.Swap ⟨1, by decide⟩),
   opAt 3837 .SUB,
   opAt 3838 (.Dup ⟨2, by decide⟩),
   opAt 3839 (.Dup ⟨1, by decide⟩),
   opAt 3840 .SUB,
   opAt 3841 (.Swap ⟨2, by decide⟩),
   opAt 3842 .GT,
   opAt 3843 .OR,
   opAt 3844 (.Swap ⟨0, by decide⟩),
   pushAt 3845 2 3264,
   opAt 3846 .MSTORE]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3847 2 4320,
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
   opAt 3859 (.Swap ⟨2, by decide⟩),
   opAt 3860 .GT,
   opAt 3861 .OR,
   opAt 3862 (.Swap ⟨0, by decide⟩),
   pushAt 3863 2 3232,
   opAt 3864 .MSTORE]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3865 2 4288,
   opAt 3866 .MLOAD,
   pushAt 3867 1 128,
   opAt 3868 .MLOAD,
   opAt 3869 (.Dup ⟨1, by decide⟩),
   opAt 3870 (.Dup ⟨1, by decide⟩),
   opAt 3871 .GT,
   opAt 3872 (.Swap ⟨1, by decide⟩),
   opAt 3873 .SUB,
   opAt 3874 (.Dup ⟨2, by decide⟩),
   opAt 3875 (.Dup ⟨1, by decide⟩),
   opAt 3876 .SUB,
   opAt 3877 (.Swap ⟨2, by decide⟩),
   opAt 3878 .GT,
   opAt 3879 .OR,
   opAt 3880 (.Swap ⟨0, by decide⟩),
   pushAt 3881 2 3200,
   opAt 3882 .MSTORE]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 3883 2 4256,
   opAt 3884 .MLOAD,
   pushAt 3885 1 96,
   opAt 3886 .MLOAD,
   opAt 3887 (.Dup ⟨1, by decide⟩),
   opAt 3888 (.Dup ⟨1, by decide⟩),
   opAt 3889 .GT,
   opAt 3890 (.Swap ⟨1, by decide⟩),
   opAt 3891 .SUB,
   opAt 3892 (.Dup ⟨2, by decide⟩),
   opAt 3893 (.Dup ⟨1, by decide⟩),
   opAt 3894 .SUB,
   opAt 3895 (.Swap ⟨2, by decide⟩),
   opAt 3896 .GT,
   opAt 3897 .OR,
   opAt 3898 (.Swap ⟨0, by decide⟩),
   pushAt 3899 2 3168,
   opAt 3900 .MSTORE]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3901 .JUMPDEST,
   pushAt 3902 2 4224,
   opAt 3903 .MLOAD,
   pushAt 3904 1 64,
   opAt 3905 .MLOAD,
   opAt 3906 (.Dup ⟨1, by decide⟩),
   opAt 3907 (.Dup ⟨1, by decide⟩),
   opAt 3908 .GT,
   opAt 3909 (.Swap ⟨1, by decide⟩),
   opAt 3910 .SUB,
   opAt 3911 (.Dup ⟨2, by decide⟩),
   opAt 3912 (.Dup ⟨1, by decide⟩),
   opAt 3913 .SUB,
   opAt 3914 (.Swap ⟨2, by decide⟩),
   opAt 3915 .GT,
   opAt 3916 .OR,
   opAt 3917 (.Swap ⟨0, by decide⟩),
   pushAt 3918 2 3136,
   opAt 3919 .MSTORE]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3920 2 4192,
   opAt 3921 .MLOAD,
   pushAt 3922 1 32,
   opAt 3923 .MLOAD,
   opAt 3924 (.Dup ⟨1, by decide⟩),
   opAt 3925 (.Dup ⟨1, by decide⟩),
   opAt 3926 .GT,
   opAt 3927 (.Swap ⟨1, by decide⟩),
   opAt 3928 .SUB,
   opAt 3929 (.Dup ⟨2, by decide⟩),
   opAt 3930 (.Dup ⟨1, by decide⟩),
   opAt 3931 .SUB,
   opAt 3932 (.Swap ⟨2, by decide⟩),
   opAt 3933 .GT,
   opAt 3934 .OR,
   opAt 3935 (.Swap ⟨0, by decide⟩),
   pushAt 3936 2 3104,
   opAt 3937 .MSTORE]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3938 2 4160,
   opAt 3939 .MLOAD,
   pushAt 3940 0 0,
   opAt 3941 .MLOAD,
   opAt 3942 (.Dup ⟨1, by decide⟩),
   opAt 3943 (.Dup ⟨1, by decide⟩),
   opAt 3944 .GT,
   opAt 3945 (.Swap ⟨1, by decide⟩),
   opAt 3946 .SUB,
   opAt 3947 (.Dup ⟨2, by decide⟩),
   opAt 3948 (.Dup ⟨1, by decide⟩),
   opAt 3949 .SUB,
   opAt 3950 (.Swap ⟨2, by decide⟩),
   opAt 3951 .GT,
   opAt 3952 .OR,
   opAt 3953 (.Swap ⟨0, by decide⟩),
   pushAt 3954 2 3072,
   opAt 3955 .MSTORE]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3956 .ISZERO,
   pushAt 3957 2 4128,
   opAt 3958 .MLOAD,
   opAt 3959 .OR,
   pushAt 3960 2 1087,
   opAt 3961 .NOT,
   pushAt 3962 2 5247,
   opAt 3963 .JUMP,
   opAt 3971 .JUMPDEST,
   opAt 3972 .MUL,
   pushAt 3973 2 4160,
   opAt 3974 .ADD,
   pushAt 3975 2 5248,
   opAt 3976 .MLOAD,
   opAt 3977 (.Swap ⟨1, by decide⟩),
   opAt 3978 .MCOPY,
   opAt 3979 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3677 2 4256,
   opAt 3678 .MLOAD,
   pushAt 3679 1 96,
   opAt 3680 .MLOAD,
   opAt 3681 (.Dup ⟨1, by decide⟩),
   opAt 3682 (.Dup ⟨1, by decide⟩),
   opAt 3683 .GT,
   opAt 3684 (.Swap ⟨1, by decide⟩),
   opAt 3685 .SUB,
   pushAt 3686 2 3168,
   opAt 3687 .MSTORE,
   pushAt 3688 2 5153,
   opAt 3689 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3901 .JUMPDEST,
   pushAt 3902 2 4224,
   opAt 3903 .MLOAD,
   pushAt 3904 1 64,
   opAt 3905 .MLOAD,
   opAt 3906 (.Dup ⟨1, by decide⟩),
   opAt 3907 (.Dup ⟨1, by decide⟩),
   opAt 3908 .GT,
   opAt 3909 (.Swap ⟨1, by decide⟩),
   opAt 3910 .SUB,
   opAt 3911 (.Dup ⟨2, by decide⟩),
   opAt 3912 (.Dup ⟨1, by decide⟩),
   opAt 3913 .SUB,
   opAt 3914 (.Swap ⟨2, by decide⟩),
   opAt 3915 .GT,
   opAt 3916 .OR,
   opAt 3917 (.Swap ⟨0, by decide⟩),
   pushAt 3918 2 3136,
   opAt 3919 .MSTORE]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3920 2 4192,
   opAt 3921 .MLOAD,
   pushAt 3922 1 32,
   opAt 3923 .MLOAD,
   opAt 3924 (.Dup ⟨1, by decide⟩),
   opAt 3925 (.Dup ⟨1, by decide⟩),
   opAt 3926 .GT,
   opAt 3927 (.Swap ⟨1, by decide⟩),
   opAt 3928 .SUB,
   opAt 3929 (.Dup ⟨2, by decide⟩),
   opAt 3930 (.Dup ⟨1, by decide⟩),
   opAt 3931 .SUB,
   opAt 3932 (.Swap ⟨2, by decide⟩),
   opAt 3933 .GT,
   opAt 3934 .OR,
   opAt 3935 (.Swap ⟨0, by decide⟩),
   pushAt 3936 2 3104,
   opAt 3937 .MSTORE]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3938 2 4160,
   opAt 3939 .MLOAD,
   pushAt 3940 0 0,
   opAt 3941 .MLOAD,
   opAt 3942 (.Dup ⟨1, by decide⟩),
   opAt 3943 (.Dup ⟨1, by decide⟩),
   opAt 3944 .GT,
   opAt 3945 (.Swap ⟨1, by decide⟩),
   opAt 3946 .SUB,
   opAt 3947 (.Dup ⟨2, by decide⟩),
   opAt 3948 (.Dup ⟨1, by decide⟩),
   opAt 3949 .SUB,
   opAt 3950 (.Swap ⟨2, by decide⟩),
   opAt 3951 .GT,
   opAt 3952 .OR,
   opAt 3953 (.Swap ⟨0, by decide⟩),
   pushAt 3954 2 3072,
   opAt 3955 .MSTORE]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3956 .ISZERO,
   pushAt 3957 2 4128,
   opAt 3958 .MLOAD,
   opAt 3959 .OR,
   pushAt 3960 2 1087,
   opAt 3961 .NOT,
   pushAt 3962 2 5247,
   opAt 3963 .JUMP,
   opAt 3971 .JUMPDEST,
   opAt 3972 .MUL,
   pushAt 3973 2 4160,
   opAt 3974 .ADD,
   pushAt 3975 2 5248,
   opAt 3976 .MLOAD,
   opAt 3977 (.Swap ⟨1, by decide⟩),
   opAt 3978 .MCOPY,
   opAt 3979 .JUMP]

@[simp] theorem fixedPC1618 : Artifact.submissionArtifact.instructionPC 1551 = 2116 := by rfl

@[simp] theorem fixedPC1619 : Artifact.submissionArtifact.instructionPC 1552 = 2119 := by
  calc
    Artifact.submissionArtifact.instructionPC 1552 =
        Artifact.submissionArtifact.instructionPC 1551 + (YulEvmCompiler.Instr.push 2 4824).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1551 _ (by rfl)
    _ = 2119 := by rw [fixedPC1618]; rfl

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3790 = 4996 := by rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4996 = true := by
  simpa only [Artifact.instructionPC, fixedPC3777] using Artifact.isValidJumpDest_index 3790 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3791 = 4997 := by
  calc
    Artifact.submissionArtifact.instructionPC 3791 =
        Artifact.submissionArtifact.instructionPC 3790 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3790 _ (by rfl)
    _ = 4997 := by rw [fixedPC3777]; rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3792 = 5000 := by
  calc
    Artifact.submissionArtifact.instructionPC 3792 =
        Artifact.submissionArtifact.instructionPC 3791 + (YulEvmCompiler.Instr.push 2 5248).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3791 _ (by rfl)
    _ = 5000 := by rw [fixedPC3778]; rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3793 = 5001 := by
  calc
    Artifact.submissionArtifact.instructionPC 3793 =
        Artifact.submissionArtifact.instructionPC 3792 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3792 _ (by rfl)
    _ = 5001 := by rw [fixedPC3779]; rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3794 = 5004 := by
  calc
    Artifact.submissionArtifact.instructionPC 3794 =
        Artifact.submissionArtifact.instructionPC 3793 + (YulEvmCompiler.Instr.push 2 256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3793 _ (by rfl)
    _ = 5004 := by rw [fixedPC3780]; rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3795 = 5005 := by
  calc
    Artifact.submissionArtifact.instructionPC 3795 =
        Artifact.submissionArtifact.instructionPC 3794 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3794 _ (by rfl)
    _ = 5005 := by rw [fixedPC3781]; rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3796 = 5008 := by
  calc
    Artifact.submissionArtifact.instructionPC 3796 =
        Artifact.submissionArtifact.instructionPC 3795 + (YulEvmCompiler.Instr.push 2 5044).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3795 _ (by rfl)
    _ = 5008 := by rw [fixedPC3782]; rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3797 = 5009 := by
  calc
    Artifact.submissionArtifact.instructionPC 3797 =
        Artifact.submissionArtifact.instructionPC 3796 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3796 _ (by rfl)
    _ = 5009 := by rw [fixedPC3783]; rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3798 = 5012 := by
  calc
    Artifact.submissionArtifact.instructionPC 3798 =
        Artifact.submissionArtifact.instructionPC 3797 + (YulEvmCompiler.Instr.push 2 5248).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3797 _ (by rfl)
    _ = 5012 := by rw [fixedPC3784]; rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3799 = 5013 := by
  calc
    Artifact.submissionArtifact.instructionPC 3799 =
        Artifact.submissionArtifact.instructionPC 3798 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3798 _ (by rfl)
    _ = 5013 := by rw [fixedPC3785]; rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3800 = 5015 := by
  calc
    Artifact.submissionArtifact.instructionPC 3800 =
        Artifact.submissionArtifact.instructionPC 3799 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3799 _ (by rfl)
    _ = 5015 := by rw [fixedPC3786]; rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3801 = 5016 := by
  calc
    Artifact.submissionArtifact.instructionPC 3801 =
        Artifact.submissionArtifact.instructionPC 3800 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3800 _ (by rfl)
    _ = 5016 := by rw [fixedPC3787]; rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3802 = 5019 := by
  calc
    Artifact.submissionArtifact.instructionPC 3802 =
        Artifact.submissionArtifact.instructionPC 3801 + (YulEvmCompiler.Instr.push 2 4846).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3801 _ (by rfl)
    _ = 5019 := by rw [fixedPC3788]; rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3803 = 5020 := by
  calc
    Artifact.submissionArtifact.instructionPC 3803 =
        Artifact.submissionArtifact.instructionPC 3802 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3802 _ (by rfl)
    _ = 5020 := by rw [fixedPC3789]; rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3804 = 5023 := by
  calc
    Artifact.submissionArtifact.instructionPC 3804 =
        Artifact.submissionArtifact.instructionPC 3803 + (YulEvmCompiler.Instr.push 2 5344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3803 _ (by rfl)
    _ = 5023 := by rw [fixedPC3790]; rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3805 = 5024 := by
  calc
    Artifact.submissionArtifact.instructionPC 3805 =
        Artifact.submissionArtifact.instructionPC 3804 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3804 _ (by rfl)
    _ = 5024 := by rw [fixedPC3791]; rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3806 = 5027 := by
  calc
    Artifact.submissionArtifact.instructionPC 3806 =
        Artifact.submissionArtifact.instructionPC 3805 + (YulEvmCompiler.Instr.push 2 5312).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3805 _ (by rfl)
    _ = 5027 := by rw [fixedPC3792]; rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3807 = 5028 := by
  calc
    Artifact.submissionArtifact.instructionPC 3807 =
        Artifact.submissionArtifact.instructionPC 3806 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3806 _ (by rfl)
    _ = 5028 := by rw [fixedPC3793]; rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3808 = 5029 := by
  calc
    Artifact.submissionArtifact.instructionPC 3808 =
        Artifact.submissionArtifact.instructionPC 3807 + (YulEvmCompiler.Instr.op (.Dup ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3807 _ (by rfl)
    _ = 5029 := by rw [fixedPC3794]; rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3809 = 5032 := by
  calc
    Artifact.submissionArtifact.instructionPC 3809 =
        Artifact.submissionArtifact.instructionPC 3808 + (YulEvmCompiler.Instr.push 2 3072).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3808 _ (by rfl)
    _ = 5032 := by rw [fixedPC3795]; rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3810 = 5033 := by
  calc
    Artifact.submissionArtifact.instructionPC 3810 =
        Artifact.submissionArtifact.instructionPC 3809 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3809 _ (by rfl)
    _ = 5033 := by rw [fixedPC3796]; rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3811 = 5036 := by
  calc
    Artifact.submissionArtifact.instructionPC 3811 =
        Artifact.submissionArtifact.instructionPC 3810 + (YulEvmCompiler.Instr.push 2 4160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3810 _ (by rfl)
    _ = 5036 := by rw [fixedPC3797]; rfl

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3812 = 5037 := by
  calc
    Artifact.submissionArtifact.instructionPC 3812 =
        Artifact.submissionArtifact.instructionPC 3811 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3811 _ (by rfl)
    _ = 5037 := by rw [fixedPC3798]; rfl

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3813 = 5038 := by
  calc
    Artifact.submissionArtifact.instructionPC 3813 =
        Artifact.submissionArtifact.instructionPC 3812 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3812 _ (by rfl)
    _ = 5038 := by rw [fixedPC3799]; rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3814 = 5039 := by
  calc
    Artifact.submissionArtifact.instructionPC 3814 =
        Artifact.submissionArtifact.instructionPC 3813 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3813 _ (by rfl)
    _ = 5039 := by rw [fixedPC3800]; rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3815 = 5040 := by
  calc
    Artifact.submissionArtifact.instructionPC 3815 =
        Artifact.submissionArtifact.instructionPC 3814 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3814 _ (by rfl)
    _ = 5040 := by rw [fixedPC3801]; rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3816 = 5043 := by
  calc
    Artifact.submissionArtifact.instructionPC 3816 =
        Artifact.submissionArtifact.instructionPC 3815 + (YulEvmCompiler.Instr.push 2 2120).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3815 _ (by rfl)
    _ = 5043 := by rw [fixedPC3802]; rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3817 = 5044 := by
  calc
    Artifact.submissionArtifact.instructionPC 3817 =
        Artifact.submissionArtifact.instructionPC 3816 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3816 _ (by rfl)
    _ = 5044 := by rw [fixedPC3803]; rfl

@[simp] theorem fixedJump5023 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5044 = true := by
  simpa only [Artifact.instructionPC, fixedPC3804] using Artifact.isValidJumpDest_index 3817 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3818 = 5045 := by
  calc
    Artifact.submissionArtifact.instructionPC 3818 =
        Artifact.submissionArtifact.instructionPC 3817 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3817 _ (by rfl)
    _ = 5045 := by rw [fixedPC3804]; rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3819 = 5048 := by
  calc
    Artifact.submissionArtifact.instructionPC 3819 =
        Artifact.submissionArtifact.instructionPC 3818 + (YulEvmCompiler.Instr.push 2 4384).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3818 _ (by rfl)
    _ = 5048 := by rw [fixedPC3805]; rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3820 = 5049 := by
  calc
    Artifact.submissionArtifact.instructionPC 3820 =
        Artifact.submissionArtifact.instructionPC 3819 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3819 _ (by rfl)
    _ = 5049 := by rw [fixedPC3806]; rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3821 = 5051 := by
  calc
    Artifact.submissionArtifact.instructionPC 3821 =
        Artifact.submissionArtifact.instructionPC 3820 + (YulEvmCompiler.Instr.push 1 224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3820 _ (by rfl)
    _ = 5051 := by rw [fixedPC3807]; rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3822 = 5052 := by
  calc
    Artifact.submissionArtifact.instructionPC 3822 =
        Artifact.submissionArtifact.instructionPC 3821 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3821 _ (by rfl)
    _ = 5052 := by rw [fixedPC3808]; rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3823 = 5053 := by
  calc
    Artifact.submissionArtifact.instructionPC 3823 =
        Artifact.submissionArtifact.instructionPC 3822 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3822 _ (by rfl)
    _ = 5053 := by rw [fixedPC3809]; rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3824 = 5054 := by
  calc
    Artifact.submissionArtifact.instructionPC 3824 =
        Artifact.submissionArtifact.instructionPC 3823 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3823 _ (by rfl)
    _ = 5054 := by rw [fixedPC3810]; rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3825 = 5055 := by
  calc
    Artifact.submissionArtifact.instructionPC 3825 =
        Artifact.submissionArtifact.instructionPC 3824 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3824 _ (by rfl)
    _ = 5055 := by rw [fixedPC3811]; rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3826 = 5056 := by
  calc
    Artifact.submissionArtifact.instructionPC 3826 =
        Artifact.submissionArtifact.instructionPC 3825 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3825 _ (by rfl)
    _ = 5056 := by rw [fixedPC3812]; rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3827 = 5057 := by
  calc
    Artifact.submissionArtifact.instructionPC 3827 =
        Artifact.submissionArtifact.instructionPC 3826 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3826 _ (by rfl)
    _ = 5057 := by rw [fixedPC3813]; rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3828 = 5060 := by
  calc
    Artifact.submissionArtifact.instructionPC 3828 =
        Artifact.submissionArtifact.instructionPC 3827 + (YulEvmCompiler.Instr.push 2 3296).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3827 _ (by rfl)
    _ = 5060 := by rw [fixedPC3814]; rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3829 = 5061 := by
  calc
    Artifact.submissionArtifact.instructionPC 3829 =
        Artifact.submissionArtifact.instructionPC 3828 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3828 _ (by rfl)
    _ = 5061 := by rw [fixedPC3815]; rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3830 = 5064 := by
  calc
    Artifact.submissionArtifact.instructionPC 3830 =
        Artifact.submissionArtifact.instructionPC 3829 + (YulEvmCompiler.Instr.push 2 4352).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3829 _ (by rfl)
    _ = 5064 := by rw [fixedPC3816]; rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3831 = 5065 := by
  calc
    Artifact.submissionArtifact.instructionPC 3831 =
        Artifact.submissionArtifact.instructionPC 3830 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3830 _ (by rfl)
    _ = 5065 := by rw [fixedPC3817]; rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3832 = 5067 := by
  calc
    Artifact.submissionArtifact.instructionPC 3832 =
        Artifact.submissionArtifact.instructionPC 3831 + (YulEvmCompiler.Instr.push 1 192).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3831 _ (by rfl)
    _ = 5067 := by rw [fixedPC3818]; rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3833 = 5068 := by
  calc
    Artifact.submissionArtifact.instructionPC 3833 =
        Artifact.submissionArtifact.instructionPC 3832 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3832 _ (by rfl)
    _ = 5068 := by rw [fixedPC3819]; rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3834 = 5069 := by
  calc
    Artifact.submissionArtifact.instructionPC 3834 =
        Artifact.submissionArtifact.instructionPC 3833 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3833 _ (by rfl)
    _ = 5069 := by rw [fixedPC3820]; rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3835 = 5070 := by
  calc
    Artifact.submissionArtifact.instructionPC 3835 =
        Artifact.submissionArtifact.instructionPC 3834 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3834 _ (by rfl)
    _ = 5070 := by rw [fixedPC3821]; rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3836 = 5071 := by
  calc
    Artifact.submissionArtifact.instructionPC 3836 =
        Artifact.submissionArtifact.instructionPC 3835 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3835 _ (by rfl)
    _ = 5071 := by rw [fixedPC3822]; rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3837 = 5072 := by
  calc
    Artifact.submissionArtifact.instructionPC 3837 =
        Artifact.submissionArtifact.instructionPC 3836 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3836 _ (by rfl)
    _ = 5072 := by rw [fixedPC3823]; rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3838 = 5073 := by
  calc
    Artifact.submissionArtifact.instructionPC 3838 =
        Artifact.submissionArtifact.instructionPC 3837 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3837 _ (by rfl)
    _ = 5073 := by rw [fixedPC3824]; rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3839 = 5074 := by
  calc
    Artifact.submissionArtifact.instructionPC 3839 =
        Artifact.submissionArtifact.instructionPC 3838 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3838 _ (by rfl)
    _ = 5074 := by rw [fixedPC3825]; rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3840 = 5075 := by
  calc
    Artifact.submissionArtifact.instructionPC 3840 =
        Artifact.submissionArtifact.instructionPC 3839 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3839 _ (by rfl)
    _ = 5075 := by rw [fixedPC3826]; rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3841 = 5076 := by
  calc
    Artifact.submissionArtifact.instructionPC 3841 =
        Artifact.submissionArtifact.instructionPC 3840 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3840 _ (by rfl)
    _ = 5076 := by rw [fixedPC3827]; rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3842 = 5077 := by
  calc
    Artifact.submissionArtifact.instructionPC 3842 =
        Artifact.submissionArtifact.instructionPC 3841 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3841 _ (by rfl)
    _ = 5077 := by rw [fixedPC3828]; rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3843 = 5078 := by
  calc
    Artifact.submissionArtifact.instructionPC 3843 =
        Artifact.submissionArtifact.instructionPC 3842 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3842 _ (by rfl)
    _ = 5078 := by rw [fixedPC3829]; rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3844 = 5079 := by
  calc
    Artifact.submissionArtifact.instructionPC 3844 =
        Artifact.submissionArtifact.instructionPC 3843 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3843 _ (by rfl)
    _ = 5079 := by rw [fixedPC3830]; rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3845 = 5080 := by
  calc
    Artifact.submissionArtifact.instructionPC 3845 =
        Artifact.submissionArtifact.instructionPC 3844 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3844 _ (by rfl)
    _ = 5080 := by rw [fixedPC3831]; rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3846 = 5083 := by
  calc
    Artifact.submissionArtifact.instructionPC 3846 =
        Artifact.submissionArtifact.instructionPC 3845 + (YulEvmCompiler.Instr.push 2 3264).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3845 _ (by rfl)
    _ = 5083 := by rw [fixedPC3832]; rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3847 = 5084 := by
  calc
    Artifact.submissionArtifact.instructionPC 3847 =
        Artifact.submissionArtifact.instructionPC 3846 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3846 _ (by rfl)
    _ = 5084 := by rw [fixedPC3833]; rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3848 = 5087 := by
  calc
    Artifact.submissionArtifact.instructionPC 3848 =
        Artifact.submissionArtifact.instructionPC 3847 + (YulEvmCompiler.Instr.push 2 4320).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3847 _ (by rfl)
    _ = 5087 := by rw [fixedPC3834]; rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3849 = 5088 := by
  calc
    Artifact.submissionArtifact.instructionPC 3849 =
        Artifact.submissionArtifact.instructionPC 3848 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3848 _ (by rfl)
    _ = 5088 := by rw [fixedPC3835]; rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3850 = 5090 := by
  calc
    Artifact.submissionArtifact.instructionPC 3850 =
        Artifact.submissionArtifact.instructionPC 3849 + (YulEvmCompiler.Instr.push 1 160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3849 _ (by rfl)
    _ = 5090 := by rw [fixedPC3836]; rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3851 = 5091 := by
  calc
    Artifact.submissionArtifact.instructionPC 3851 =
        Artifact.submissionArtifact.instructionPC 3850 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3850 _ (by rfl)
    _ = 5091 := by rw [fixedPC3837]; rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3852 = 5092 := by
  calc
    Artifact.submissionArtifact.instructionPC 3852 =
        Artifact.submissionArtifact.instructionPC 3851 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3851 _ (by rfl)
    _ = 5092 := by rw [fixedPC3838]; rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3853 = 5093 := by
  calc
    Artifact.submissionArtifact.instructionPC 3853 =
        Artifact.submissionArtifact.instructionPC 3852 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3852 _ (by rfl)
    _ = 5093 := by rw [fixedPC3839]; rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3854 = 5094 := by
  calc
    Artifact.submissionArtifact.instructionPC 3854 =
        Artifact.submissionArtifact.instructionPC 3853 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3853 _ (by rfl)
    _ = 5094 := by rw [fixedPC3840]; rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3855 = 5095 := by
  calc
    Artifact.submissionArtifact.instructionPC 3855 =
        Artifact.submissionArtifact.instructionPC 3854 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3854 _ (by rfl)
    _ = 5095 := by rw [fixedPC3841]; rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3856 = 5096 := by
  calc
    Artifact.submissionArtifact.instructionPC 3856 =
        Artifact.submissionArtifact.instructionPC 3855 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3855 _ (by rfl)
    _ = 5096 := by rw [fixedPC3842]; rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3857 = 5097 := by
  calc
    Artifact.submissionArtifact.instructionPC 3857 =
        Artifact.submissionArtifact.instructionPC 3856 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3856 _ (by rfl)
    _ = 5097 := by rw [fixedPC3843]; rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3858 = 5098 := by
  calc
    Artifact.submissionArtifact.instructionPC 3858 =
        Artifact.submissionArtifact.instructionPC 3857 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3857 _ (by rfl)
    _ = 5098 := by rw [fixedPC3844]; rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3859 = 5099 := by
  calc
    Artifact.submissionArtifact.instructionPC 3859 =
        Artifact.submissionArtifact.instructionPC 3858 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3858 _ (by rfl)
    _ = 5099 := by rw [fixedPC3845]; rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3860 = 5100 := by
  calc
    Artifact.submissionArtifact.instructionPC 3860 =
        Artifact.submissionArtifact.instructionPC 3859 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3859 _ (by rfl)
    _ = 5100 := by rw [fixedPC3846]; rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3861 = 5101 := by
  calc
    Artifact.submissionArtifact.instructionPC 3861 =
        Artifact.submissionArtifact.instructionPC 3860 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3860 _ (by rfl)
    _ = 5101 := by rw [fixedPC3847]; rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3862 = 5102 := by
  calc
    Artifact.submissionArtifact.instructionPC 3862 =
        Artifact.submissionArtifact.instructionPC 3861 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3861 _ (by rfl)
    _ = 5102 := by rw [fixedPC3848]; rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3863 = 5103 := by
  calc
    Artifact.submissionArtifact.instructionPC 3863 =
        Artifact.submissionArtifact.instructionPC 3862 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3862 _ (by rfl)
    _ = 5103 := by rw [fixedPC3849]; rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3864 = 5106 := by
  calc
    Artifact.submissionArtifact.instructionPC 3864 =
        Artifact.submissionArtifact.instructionPC 3863 + (YulEvmCompiler.Instr.push 2 3232).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3863 _ (by rfl)
    _ = 5106 := by rw [fixedPC3850]; rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3865 = 5107 := by
  calc
    Artifact.submissionArtifact.instructionPC 3865 =
        Artifact.submissionArtifact.instructionPC 3864 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3864 _ (by rfl)
    _ = 5107 := by rw [fixedPC3851]; rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3866 = 5110 := by
  calc
    Artifact.submissionArtifact.instructionPC 3866 =
        Artifact.submissionArtifact.instructionPC 3865 + (YulEvmCompiler.Instr.push 2 4288).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3865 _ (by rfl)
    _ = 5110 := by rw [fixedPC3852]; rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3867 = 5111 := by
  calc
    Artifact.submissionArtifact.instructionPC 3867 =
        Artifact.submissionArtifact.instructionPC 3866 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3866 _ (by rfl)
    _ = 5111 := by rw [fixedPC3853]; rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3868 = 5113 := by
  calc
    Artifact.submissionArtifact.instructionPC 3868 =
        Artifact.submissionArtifact.instructionPC 3867 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3867 _ (by rfl)
    _ = 5113 := by rw [fixedPC3854]; rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3869 = 5114 := by
  calc
    Artifact.submissionArtifact.instructionPC 3869 =
        Artifact.submissionArtifact.instructionPC 3868 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3868 _ (by rfl)
    _ = 5114 := by rw [fixedPC3855]; rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3870 = 5115 := by
  calc
    Artifact.submissionArtifact.instructionPC 3870 =
        Artifact.submissionArtifact.instructionPC 3869 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3869 _ (by rfl)
    _ = 5115 := by rw [fixedPC3856]; rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3871 = 5116 := by
  calc
    Artifact.submissionArtifact.instructionPC 3871 =
        Artifact.submissionArtifact.instructionPC 3870 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3870 _ (by rfl)
    _ = 5116 := by rw [fixedPC3857]; rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3872 = 5117 := by
  calc
    Artifact.submissionArtifact.instructionPC 3872 =
        Artifact.submissionArtifact.instructionPC 3871 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3871 _ (by rfl)
    _ = 5117 := by rw [fixedPC3858]; rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3873 = 5118 := by
  calc
    Artifact.submissionArtifact.instructionPC 3873 =
        Artifact.submissionArtifact.instructionPC 3872 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3872 _ (by rfl)
    _ = 5118 := by rw [fixedPC3859]; rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3874 = 5119 := by
  calc
    Artifact.submissionArtifact.instructionPC 3874 =
        Artifact.submissionArtifact.instructionPC 3873 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3873 _ (by rfl)
    _ = 5119 := by rw [fixedPC3860]; rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3875 = 5120 := by
  calc
    Artifact.submissionArtifact.instructionPC 3875 =
        Artifact.submissionArtifact.instructionPC 3874 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3874 _ (by rfl)
    _ = 5120 := by rw [fixedPC3861]; rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3876 = 5121 := by
  calc
    Artifact.submissionArtifact.instructionPC 3876 =
        Artifact.submissionArtifact.instructionPC 3875 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3875 _ (by rfl)
    _ = 5121 := by rw [fixedPC3862]; rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3877 = 5122 := by
  calc
    Artifact.submissionArtifact.instructionPC 3877 =
        Artifact.submissionArtifact.instructionPC 3876 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3876 _ (by rfl)
    _ = 5122 := by rw [fixedPC3863]; rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3878 = 5123 := by
  calc
    Artifact.submissionArtifact.instructionPC 3878 =
        Artifact.submissionArtifact.instructionPC 3877 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3877 _ (by rfl)
    _ = 5123 := by rw [fixedPC3864]; rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3879 = 5124 := by
  calc
    Artifact.submissionArtifact.instructionPC 3879 =
        Artifact.submissionArtifact.instructionPC 3878 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3878 _ (by rfl)
    _ = 5124 := by rw [fixedPC3865]; rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3880 = 5125 := by
  calc
    Artifact.submissionArtifact.instructionPC 3880 =
        Artifact.submissionArtifact.instructionPC 3879 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3879 _ (by rfl)
    _ = 5125 := by rw [fixedPC3866]; rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3881 = 5126 := by
  calc
    Artifact.submissionArtifact.instructionPC 3881 =
        Artifact.submissionArtifact.instructionPC 3880 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3880 _ (by rfl)
    _ = 5126 := by rw [fixedPC3867]; rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3882 = 5129 := by
  calc
    Artifact.submissionArtifact.instructionPC 3882 =
        Artifact.submissionArtifact.instructionPC 3881 + (YulEvmCompiler.Instr.push 2 3200).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3881 _ (by rfl)
    _ = 5129 := by rw [fixedPC3868]; rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3883 = 5130 := by
  calc
    Artifact.submissionArtifact.instructionPC 3883 =
        Artifact.submissionArtifact.instructionPC 3882 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3882 _ (by rfl)
    _ = 5130 := by rw [fixedPC3869]; rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3884 = 5133 := by
  calc
    Artifact.submissionArtifact.instructionPC 3884 =
        Artifact.submissionArtifact.instructionPC 3883 + (YulEvmCompiler.Instr.push 2 4256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3883 _ (by rfl)
    _ = 5133 := by rw [fixedPC3871]; rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3885 = 5134 := by
  calc
    Artifact.submissionArtifact.instructionPC 3885 =
        Artifact.submissionArtifact.instructionPC 3884 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3884 _ (by rfl)
    _ = 5134 := by rw [fixedPC3872]; rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3886 = 5136 := by
  calc
    Artifact.submissionArtifact.instructionPC 3886 =
        Artifact.submissionArtifact.instructionPC 3885 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3885 _ (by rfl)
    _ = 5136 := by rw [fixedPC3873]; rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3887 = 5137 := by
  calc
    Artifact.submissionArtifact.instructionPC 3887 =
        Artifact.submissionArtifact.instructionPC 3886 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3886 _ (by rfl)
    _ = 5137 := by rw [fixedPC3874]; rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3888 = 5138 := by
  calc
    Artifact.submissionArtifact.instructionPC 3888 =
        Artifact.submissionArtifact.instructionPC 3887 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3887 _ (by rfl)
    _ = 5138 := by rw [fixedPC3875]; rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3889 = 5139 := by
  calc
    Artifact.submissionArtifact.instructionPC 3889 =
        Artifact.submissionArtifact.instructionPC 3888 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3888 _ (by rfl)
    _ = 5139 := by rw [fixedPC3876]; rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3890 = 5140 := by
  calc
    Artifact.submissionArtifact.instructionPC 3890 =
        Artifact.submissionArtifact.instructionPC 3889 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3889 _ (by rfl)
    _ = 5140 := by rw [fixedPC3877]; rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3891 = 5141 := by
  calc
    Artifact.submissionArtifact.instructionPC 3891 =
        Artifact.submissionArtifact.instructionPC 3890 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3890 _ (by rfl)
    _ = 5141 := by rw [fixedPC3878]; rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3892 = 5142 := by
  calc
    Artifact.submissionArtifact.instructionPC 3892 =
        Artifact.submissionArtifact.instructionPC 3891 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3891 _ (by rfl)
    _ = 5142 := by rw [fixedPC3879]; rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3893 = 5143 := by
  calc
    Artifact.submissionArtifact.instructionPC 3893 =
        Artifact.submissionArtifact.instructionPC 3892 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3892 _ (by rfl)
    _ = 5143 := by rw [fixedPC3880]; rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3894 = 5144 := by
  calc
    Artifact.submissionArtifact.instructionPC 3894 =
        Artifact.submissionArtifact.instructionPC 3893 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3893 _ (by rfl)
    _ = 5144 := by rw [fixedPC3881]; rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3895 = 5145 := by
  calc
    Artifact.submissionArtifact.instructionPC 3895 =
        Artifact.submissionArtifact.instructionPC 3894 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3894 _ (by rfl)
    _ = 5145 := by rw [fixedPC3882]; rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3896 = 5146 := by
  calc
    Artifact.submissionArtifact.instructionPC 3896 =
        Artifact.submissionArtifact.instructionPC 3895 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3895 _ (by rfl)
    _ = 5146 := by rw [fixedPC3883]; rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3897 = 5147 := by
  calc
    Artifact.submissionArtifact.instructionPC 3897 =
        Artifact.submissionArtifact.instructionPC 3896 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3896 _ (by rfl)
    _ = 5147 := by rw [fixedPC3884]; rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3898 = 5148 := by
  calc
    Artifact.submissionArtifact.instructionPC 3898 =
        Artifact.submissionArtifact.instructionPC 3897 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3897 _ (by rfl)
    _ = 5148 := by rw [fixedPC3885]; rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3899 = 5149 := by
  calc
    Artifact.submissionArtifact.instructionPC 3899 =
        Artifact.submissionArtifact.instructionPC 3898 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3898 _ (by rfl)
    _ = 5149 := by rw [fixedPC3886]; rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3900 = 5152 := by
  calc
    Artifact.submissionArtifact.instructionPC 3900 =
        Artifact.submissionArtifact.instructionPC 3899 + (YulEvmCompiler.Instr.push 2 3168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3899 _ (by rfl)
    _ = 5152 := by rw [fixedPC3887]; rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3901 = 5153 := by
  calc
    Artifact.submissionArtifact.instructionPC 3901 =
        Artifact.submissionArtifact.instructionPC 3900 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3900 _ (by rfl)
    _ = 5153 := by rw [fixedPC3888]; rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5153 = true := by
  simpa only [Artifact.instructionPC, fixedPC3889] using Artifact.isValidJumpDest_index 3901 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3902 = 5154 := by
  calc
    Artifact.submissionArtifact.instructionPC 3902 =
        Artifact.submissionArtifact.instructionPC 3901 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3901 _ (by rfl)
    _ = 5154 := by rw [fixedPC3889]; rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3903 = 5157 := by
  calc
    Artifact.submissionArtifact.instructionPC 3903 =
        Artifact.submissionArtifact.instructionPC 3902 + (YulEvmCompiler.Instr.push 2 4224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3902 _ (by rfl)
    _ = 5157 := by rw [fixedPC3890]; rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3904 = 5158 := by
  calc
    Artifact.submissionArtifact.instructionPC 3904 =
        Artifact.submissionArtifact.instructionPC 3903 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3903 _ (by rfl)
    _ = 5158 := by rw [fixedPC3891]; rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3905 = 5160 := by
  calc
    Artifact.submissionArtifact.instructionPC 3905 =
        Artifact.submissionArtifact.instructionPC 3904 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3904 _ (by rfl)
    _ = 5160 := by rw [fixedPC3892]; rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3906 = 5161 := by
  calc
    Artifact.submissionArtifact.instructionPC 3906 =
        Artifact.submissionArtifact.instructionPC 3905 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3905 _ (by rfl)
    _ = 5161 := by rw [fixedPC3893]; rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3907 = 5162 := by
  calc
    Artifact.submissionArtifact.instructionPC 3907 =
        Artifact.submissionArtifact.instructionPC 3906 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3906 _ (by rfl)
    _ = 5162 := by rw [fixedPC3894]; rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3908 = 5163 := by
  calc
    Artifact.submissionArtifact.instructionPC 3908 =
        Artifact.submissionArtifact.instructionPC 3907 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3907 _ (by rfl)
    _ = 5163 := by rw [fixedPC3895]; rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3909 = 5164 := by
  calc
    Artifact.submissionArtifact.instructionPC 3909 =
        Artifact.submissionArtifact.instructionPC 3908 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3908 _ (by rfl)
    _ = 5164 := by rw [fixedPC3896]; rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3910 = 5165 := by
  calc
    Artifact.submissionArtifact.instructionPC 3910 =
        Artifact.submissionArtifact.instructionPC 3909 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3909 _ (by rfl)
    _ = 5165 := by rw [fixedPC3897]; rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3911 = 5166 := by
  calc
    Artifact.submissionArtifact.instructionPC 3911 =
        Artifact.submissionArtifact.instructionPC 3910 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3910 _ (by rfl)
    _ = 5166 := by rw [fixedPC3898]; rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3912 = 5167 := by
  calc
    Artifact.submissionArtifact.instructionPC 3912 =
        Artifact.submissionArtifact.instructionPC 3911 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3911 _ (by rfl)
    _ = 5167 := by rw [fixedPC3899]; rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3913 = 5168 := by
  calc
    Artifact.submissionArtifact.instructionPC 3913 =
        Artifact.submissionArtifact.instructionPC 3912 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3912 _ (by rfl)
    _ = 5168 := by rw [fixedPC3900]; rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3914 = 5169 := by
  calc
    Artifact.submissionArtifact.instructionPC 3914 =
        Artifact.submissionArtifact.instructionPC 3913 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3913 _ (by rfl)
    _ = 5169 := by rw [fixedPC3901]; rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3915 = 5170 := by
  calc
    Artifact.submissionArtifact.instructionPC 3915 =
        Artifact.submissionArtifact.instructionPC 3914 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3914 _ (by rfl)
    _ = 5170 := by rw [fixedPC3902]; rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3916 = 5171 := by
  calc
    Artifact.submissionArtifact.instructionPC 3916 =
        Artifact.submissionArtifact.instructionPC 3915 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3915 _ (by rfl)
    _ = 5171 := by rw [fixedPC3903]; rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3917 = 5172 := by
  calc
    Artifact.submissionArtifact.instructionPC 3917 =
        Artifact.submissionArtifact.instructionPC 3916 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3916 _ (by rfl)
    _ = 5172 := by rw [fixedPC3904]; rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3918 = 5173 := by
  calc
    Artifact.submissionArtifact.instructionPC 3918 =
        Artifact.submissionArtifact.instructionPC 3917 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3917 _ (by rfl)
    _ = 5173 := by rw [fixedPC3905]; rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3919 = 5176 := by
  calc
    Artifact.submissionArtifact.instructionPC 3919 =
        Artifact.submissionArtifact.instructionPC 3918 + (YulEvmCompiler.Instr.push 2 3136).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3918 _ (by rfl)
    _ = 5176 := by rw [fixedPC3906]; rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3920 = 5177 := by
  calc
    Artifact.submissionArtifact.instructionPC 3920 =
        Artifact.submissionArtifact.instructionPC 3919 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3919 _ (by rfl)
    _ = 5177 := by rw [fixedPC3907]; rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3921 = 5180 := by
  calc
    Artifact.submissionArtifact.instructionPC 3921 =
        Artifact.submissionArtifact.instructionPC 3920 + (YulEvmCompiler.Instr.push 2 4192).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3920 _ (by rfl)
    _ = 5180 := by rw [fixedPC3908]; rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3922 = 5181 := by
  calc
    Artifact.submissionArtifact.instructionPC 3922 =
        Artifact.submissionArtifact.instructionPC 3921 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3921 _ (by rfl)
    _ = 5181 := by rw [fixedPC3909]; rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3923 = 5183 := by
  calc
    Artifact.submissionArtifact.instructionPC 3923 =
        Artifact.submissionArtifact.instructionPC 3922 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3922 _ (by rfl)
    _ = 5183 := by rw [fixedPC3910]; rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3924 = 5184 := by
  calc
    Artifact.submissionArtifact.instructionPC 3924 =
        Artifact.submissionArtifact.instructionPC 3923 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3923 _ (by rfl)
    _ = 5184 := by rw [fixedPC3911]; rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3925 = 5185 := by
  calc
    Artifact.submissionArtifact.instructionPC 3925 =
        Artifact.submissionArtifact.instructionPC 3924 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3924 _ (by rfl)
    _ = 5185 := by rw [fixedPC3912]; rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3926 = 5186 := by
  calc
    Artifact.submissionArtifact.instructionPC 3926 =
        Artifact.submissionArtifact.instructionPC 3925 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3925 _ (by rfl)
    _ = 5186 := by rw [fixedPC3913]; rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3927 = 5187 := by
  calc
    Artifact.submissionArtifact.instructionPC 3927 =
        Artifact.submissionArtifact.instructionPC 3926 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3926 _ (by rfl)
    _ = 5187 := by rw [fixedPC3914]; rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3928 = 5188 := by
  calc
    Artifact.submissionArtifact.instructionPC 3928 =
        Artifact.submissionArtifact.instructionPC 3927 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3927 _ (by rfl)
    _ = 5188 := by rw [fixedPC3915]; rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3929 = 5189 := by
  calc
    Artifact.submissionArtifact.instructionPC 3929 =
        Artifact.submissionArtifact.instructionPC 3928 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3928 _ (by rfl)
    _ = 5189 := by rw [fixedPC3916]; rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3930 = 5190 := by
  calc
    Artifact.submissionArtifact.instructionPC 3930 =
        Artifact.submissionArtifact.instructionPC 3929 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3929 _ (by rfl)
    _ = 5190 := by rw [fixedPC3917]; rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3931 = 5191 := by
  calc
    Artifact.submissionArtifact.instructionPC 3931 =
        Artifact.submissionArtifact.instructionPC 3930 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3930 _ (by rfl)
    _ = 5191 := by rw [fixedPC3918]; rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3932 = 5192 := by
  calc
    Artifact.submissionArtifact.instructionPC 3932 =
        Artifact.submissionArtifact.instructionPC 3931 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3931 _ (by rfl)
    _ = 5192 := by rw [fixedPC3919]; rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3933 = 5193 := by
  calc
    Artifact.submissionArtifact.instructionPC 3933 =
        Artifact.submissionArtifact.instructionPC 3932 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3932 _ (by rfl)
    _ = 5193 := by rw [fixedPC3920]; rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3934 = 5194 := by
  calc
    Artifact.submissionArtifact.instructionPC 3934 =
        Artifact.submissionArtifact.instructionPC 3933 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3933 _ (by rfl)
    _ = 5194 := by rw [fixedPC3921]; rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3935 = 5195 := by
  calc
    Artifact.submissionArtifact.instructionPC 3935 =
        Artifact.submissionArtifact.instructionPC 3934 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3934 _ (by rfl)
    _ = 5195 := by rw [fixedPC3922]; rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3936 = 5196 := by
  calc
    Artifact.submissionArtifact.instructionPC 3936 =
        Artifact.submissionArtifact.instructionPC 3935 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3935 _ (by rfl)
    _ = 5196 := by rw [fixedPC3923]; rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3937 = 5199 := by
  calc
    Artifact.submissionArtifact.instructionPC 3937 =
        Artifact.submissionArtifact.instructionPC 3936 + (YulEvmCompiler.Instr.push 2 3104).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3936 _ (by rfl)
    _ = 5199 := by rw [fixedPC3924]; rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3938 = 5200 := by
  calc
    Artifact.submissionArtifact.instructionPC 3938 =
        Artifact.submissionArtifact.instructionPC 3937 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3937 _ (by rfl)
    _ = 5200 := by rw [fixedPC3925]; rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3939 = 5203 := by
  calc
    Artifact.submissionArtifact.instructionPC 3939 =
        Artifact.submissionArtifact.instructionPC 3938 + (YulEvmCompiler.Instr.push 2 4160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3938 _ (by rfl)
    _ = 5203 := by rw [fixedPC3926]; rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3940 = 5204 := by
  calc
    Artifact.submissionArtifact.instructionPC 3940 =
        Artifact.submissionArtifact.instructionPC 3939 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3939 _ (by rfl)
    _ = 5204 := by rw [fixedPC3927]; rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3941 = 5205 := by
  calc
    Artifact.submissionArtifact.instructionPC 3941 =
        Artifact.submissionArtifact.instructionPC 3940 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3940 _ (by rfl)
    _ = 5205 := by rw [fixedPC3928]; rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3942 = 5206 := by
  calc
    Artifact.submissionArtifact.instructionPC 3942 =
        Artifact.submissionArtifact.instructionPC 3941 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3941 _ (by rfl)
    _ = 5206 := by rw [fixedPC3929]; rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3943 = 5207 := by
  calc
    Artifact.submissionArtifact.instructionPC 3943 =
        Artifact.submissionArtifact.instructionPC 3942 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3942 _ (by rfl)
    _ = 5207 := by rw [fixedPC3930]; rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3944 = 5208 := by
  calc
    Artifact.submissionArtifact.instructionPC 3944 =
        Artifact.submissionArtifact.instructionPC 3943 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3943 _ (by rfl)
    _ = 5208 := by rw [fixedPC3931]; rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3945 = 5209 := by
  calc
    Artifact.submissionArtifact.instructionPC 3945 =
        Artifact.submissionArtifact.instructionPC 3944 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3944 _ (by rfl)
    _ = 5209 := by rw [fixedPC3932]; rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3946 = 5210 := by
  calc
    Artifact.submissionArtifact.instructionPC 3946 =
        Artifact.submissionArtifact.instructionPC 3945 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3945 _ (by rfl)
    _ = 5210 := by rw [fixedPC3933]; rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3947 = 5211 := by
  calc
    Artifact.submissionArtifact.instructionPC 3947 =
        Artifact.submissionArtifact.instructionPC 3946 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3946 _ (by rfl)
    _ = 5211 := by rw [fixedPC3934]; rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3948 = 5212 := by
  calc
    Artifact.submissionArtifact.instructionPC 3948 =
        Artifact.submissionArtifact.instructionPC 3947 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3947 _ (by rfl)
    _ = 5212 := by rw [fixedPC3935]; rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3949 = 5213 := by
  calc
    Artifact.submissionArtifact.instructionPC 3949 =
        Artifact.submissionArtifact.instructionPC 3948 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3948 _ (by rfl)
    _ = 5213 := by rw [fixedPC3936]; rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3950 = 5214 := by
  calc
    Artifact.submissionArtifact.instructionPC 3950 =
        Artifact.submissionArtifact.instructionPC 3949 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3949 _ (by rfl)
    _ = 5214 := by rw [fixedPC3937]; rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3951 = 5215 := by
  calc
    Artifact.submissionArtifact.instructionPC 3951 =
        Artifact.submissionArtifact.instructionPC 3950 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3950 _ (by rfl)
    _ = 5215 := by rw [fixedPC3938]; rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3952 = 5216 := by
  calc
    Artifact.submissionArtifact.instructionPC 3952 =
        Artifact.submissionArtifact.instructionPC 3951 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3951 _ (by rfl)
    _ = 5216 := by rw [fixedPC3939]; rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3953 = 5217 := by
  calc
    Artifact.submissionArtifact.instructionPC 3953 =
        Artifact.submissionArtifact.instructionPC 3952 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3952 _ (by rfl)
    _ = 5217 := by rw [fixedPC3940]; rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3954 = 5218 := by
  calc
    Artifact.submissionArtifact.instructionPC 3954 =
        Artifact.submissionArtifact.instructionPC 3953 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3953 _ (by rfl)
    _ = 5218 := by rw [fixedPC3941]; rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3955 = 5221 := by
  calc
    Artifact.submissionArtifact.instructionPC 3955 =
        Artifact.submissionArtifact.instructionPC 3954 + (YulEvmCompiler.Instr.push 2 3072).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3954 _ (by rfl)
    _ = 5221 := by rw [fixedPC3942]; rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3956 = 5222 := by
  calc
    Artifact.submissionArtifact.instructionPC 3956 =
        Artifact.submissionArtifact.instructionPC 3955 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3955 _ (by rfl)
    _ = 5222 := by rw [fixedPC3943]; rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3957 = 5223 := by
  calc
    Artifact.submissionArtifact.instructionPC 3957 =
        Artifact.submissionArtifact.instructionPC 3956 + (YulEvmCompiler.Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3956 _ (by rfl)
    _ = 5223 := by rw [fixedPC3944]; rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3958 = 5226 := by
  calc
    Artifact.submissionArtifact.instructionPC 3958 =
        Artifact.submissionArtifact.instructionPC 3957 + (YulEvmCompiler.Instr.push 2 4128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3957 _ (by rfl)
    _ = 5226 := by rw [fixedPC3945]; rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3959 = 5227 := by
  calc
    Artifact.submissionArtifact.instructionPC 3959 =
        Artifact.submissionArtifact.instructionPC 3958 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3958 _ (by rfl)
    _ = 5227 := by rw [fixedPC3946]; rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3960 = 5228 := by
  calc
    Artifact.submissionArtifact.instructionPC 3960 =
        Artifact.submissionArtifact.instructionPC 3959 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3959 _ (by rfl)
    _ = 5228 := by rw [fixedPC3947]; rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3972 = 5248 := by
  decide

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3972 = 5248 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3973 = 5249 := by
  calc
    Artifact.submissionArtifact.instructionPC 3973 =
        Artifact.submissionArtifact.instructionPC 3972 + (YulEvmCompiler.Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3972 _ (by rfl)
    _ = 5249 := by rw [fixedPC3950]; rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3974 = 5252 := by
  calc
    Artifact.submissionArtifact.instructionPC 3974 =
        Artifact.submissionArtifact.instructionPC 3973 + (YulEvmCompiler.Instr.push 2 4160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3973 _ (by rfl)
    _ = 5252 := by rw [fixedPC3951]; rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3975 = 5253 := by
  calc
    Artifact.submissionArtifact.instructionPC 3975 =
        Artifact.submissionArtifact.instructionPC 3974 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3974 _ (by rfl)
    _ = 5253 := by rw [fixedPC3952]; rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3976 = 5256 := by
  calc
    Artifact.submissionArtifact.instructionPC 3976 =
        Artifact.submissionArtifact.instructionPC 3975 + (YulEvmCompiler.Instr.push 2 5248).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3975 _ (by rfl)
    _ = 5256 := by rw [fixedPC3953]; rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3977 = 5257 := by
  calc
    Artifact.submissionArtifact.instructionPC 3977 =
        Artifact.submissionArtifact.instructionPC 3976 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3976 _ (by rfl)
    _ = 5257 := by rw [fixedPC3954]; rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3978 = 5258 := by
  calc
    Artifact.submissionArtifact.instructionPC 3978 =
        Artifact.submissionArtifact.instructionPC 3977 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3977 _ (by rfl)
    _ = 5258 := by rw [fixedPC3955]; rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3979 = 5259 := by
  calc
    Artifact.submissionArtifact.instructionPC 3979 =
        Artifact.submissionArtifact.instructionPC 3978 + (YulEvmCompiler.Instr.op .MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3978 _ (by rfl)
    _ = 5259 := by rw [fixedPC3956]; rfl



@[simp] theorem fixedPC3959 : Artifact.submissionArtifact.instructionPC 0 = 0 := by rfl

@[simp] theorem fixedPC3960 : Artifact.submissionArtifact.instructionPC 1 = 1 := by rfl

@[simp] theorem fixedPC3961 : Artifact.submissionArtifact.instructionPC 2 = 2 := by rfl

@[simp] theorem fixedPC3962 : Artifact.submissionArtifact.instructionPC 3 = 4 := by rfl

@[simp] theorem fixedPC3963 : Artifact.submissionArtifact.instructionPC 4 = 5 := by rfl

@[simp] theorem fixedPC3964 : Artifact.submissionArtifact.instructionPC 5 = 7 := by rfl

@[simp] theorem fixedPC3965 : Artifact.submissionArtifact.instructionPC 6 = 8 := by rfl

@[simp] theorem fixedPC3966 : Artifact.submissionArtifact.instructionPC 7 = 10 := by rfl

@[simp] theorem fixedPC3967 : Artifact.submissionArtifact.instructionPC 8 = 11 := by rfl

@[simp] theorem fixedPC3968 : Artifact.submissionArtifact.instructionPC 9 = 12 := by rfl

@[simp] theorem fixedPC3969 : Artifact.submissionArtifact.instructionPC 10 = 13 := by rfl

@[simp] theorem fixedPC3970 : Artifact.submissionArtifact.instructionPC 11 = 15 := by rfl

@[simp] theorem fixedPC3971 : Artifact.submissionArtifact.instructionPC 12 = 16 := by rfl

@[simp] theorem fixedPC3972 : Artifact.submissionArtifact.instructionPC 13 = 17 := by rfl

@[simp] theorem fixedPC3973 : Artifact.submissionArtifact.instructionPC 14 = 18 := by rfl

@[simp] theorem fixedPC3974 : Artifact.submissionArtifact.instructionPC 15 = 20 := by rfl

@[simp] theorem fixedPC3975 : Artifact.submissionArtifact.instructionPC 16 = 21 := by rfl

@[simp] theorem fixedPC3976 : Artifact.submissionArtifact.instructionPC 17 = 22 := by rfl

@[simp] theorem fixedPC3977 : Artifact.submissionArtifact.instructionPC 18 = 25 := by rfl

@[simp] theorem fixedPC3978 : Artifact.submissionArtifact.instructionPC 19 = 26 := by rfl

@[simp] theorem fixedPC3979 : Artifact.submissionArtifact.instructionPC 20 = 27 := by rfl

@[simp] theorem fixedPC3980 : Artifact.submissionArtifact.instructionPC 21 = 29 := by rfl

@[simp] theorem fixedPC3981 : Artifact.submissionArtifact.instructionPC 22 = 30 := by rfl

@[simp] theorem fixedPC3982 : Artifact.submissionArtifact.instructionPC 23 = 31 := by rfl

@[simp] theorem fixedPC3983 : Artifact.submissionArtifact.instructionPC 24 = 32 := by rfl

@[simp] theorem fixedPC3984 : Artifact.submissionArtifact.instructionPC 25 = 33 := by rfl

@[simp] theorem fixedPC3985 : Artifact.submissionArtifact.instructionPC 26 = 36 := by rfl

@[simp] theorem fixedPC3986 : Artifact.submissionArtifact.instructionPC 27 = 37 := by rfl

@[simp] theorem fixedPC3987 : Artifact.submissionArtifact.instructionPC 28 = 38 := by rfl

@[simp] theorem fixedPC3988 : Artifact.submissionArtifact.instructionPC 29 = 40 := by rfl

@[simp] theorem fixedPC3989 : Artifact.submissionArtifact.instructionPC 30 = 41 := by rfl

@[simp] theorem fixedPC3990 : Artifact.submissionArtifact.instructionPC 31 = 42 := by rfl



@[simp] theorem fixedPC3993 : Artifact.submissionArtifact.instructionPC 71 = 127 := by rfl

@[simp] theorem fixedJump5272 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 127 = true := by
  simpa only [Artifact.instructionPC, fixedPC3993] using Artifact.isValidJumpDest_index 71 (by rfl)

@[simp] theorem fixedPC3994 : Artifact.submissionArtifact.instructionPC 72 = 128 := by rfl

@[simp] theorem fixedPC3995 : Artifact.submissionArtifact.instructionPC 73 = 129 := by rfl

@[simp] theorem fixedPC3996 : Artifact.submissionArtifact.instructionPC 74 = 130 := by rfl

@[simp] theorem fixedPC3997 : Artifact.submissionArtifact.instructionPC 75 = 131 := by rfl

@[simp] theorem fixedPC3998 : Artifact.submissionArtifact.instructionPC 76 = 134 := by rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3676 = 4846 := by
  decide

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4846 = true := by
  simpa only [Artifact.instructionPC, fixedPC3999] using Artifact.isValidJumpDest_index 3676 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3677 = 4847 := by
  calc
    Artifact.submissionArtifact.instructionPC 3677 =
        Artifact.submissionArtifact.instructionPC 3676 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3676 _ (by rfl)
    _ = 4847 := by rw [fixedPC3999]; rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3678 = 4850 := by
  calc
    Artifact.submissionArtifact.instructionPC 3678 =
        Artifact.submissionArtifact.instructionPC 3677 + (YulEvmCompiler.Instr.push 2 4256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3677 _ (by rfl)
    _ = 4850 := by rw [fixedPC4000]; rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3679 = 4851 := by
  calc
    Artifact.submissionArtifact.instructionPC 3679 =
        Artifact.submissionArtifact.instructionPC 3678 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3678 _ (by rfl)
    _ = 4851 := by rw [fixedPC4001]; rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3680 = 4853 := by
  calc
    Artifact.submissionArtifact.instructionPC 3680 =
        Artifact.submissionArtifact.instructionPC 3679 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3679 _ (by rfl)
    _ = 4853 := by rw [fixedPC4002]; rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3681 = 4854 := by
  calc
    Artifact.submissionArtifact.instructionPC 3681 =
        Artifact.submissionArtifact.instructionPC 3680 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3680 _ (by rfl)
    _ = 4854 := by rw [fixedPC4003]; rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3682 = 4855 := by
  calc
    Artifact.submissionArtifact.instructionPC 3682 =
        Artifact.submissionArtifact.instructionPC 3681 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3681 _ (by rfl)
    _ = 4855 := by rw [fixedPC4004]; rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3683 = 4856 := by
  calc
    Artifact.submissionArtifact.instructionPC 3683 =
        Artifact.submissionArtifact.instructionPC 3682 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3682 _ (by rfl)
    _ = 4856 := by rw [fixedPC4005]; rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3684 = 4857 := by
  calc
    Artifact.submissionArtifact.instructionPC 3684 =
        Artifact.submissionArtifact.instructionPC 3683 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3683 _ (by rfl)
    _ = 4857 := by rw [fixedPC4006]; rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3685 = 4858 := by
  calc
    Artifact.submissionArtifact.instructionPC 3685 =
        Artifact.submissionArtifact.instructionPC 3684 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3684 _ (by rfl)
    _ = 4858 := by rw [fixedPC4007]; rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3686 = 4859 := by
  calc
    Artifact.submissionArtifact.instructionPC 3686 =
        Artifact.submissionArtifact.instructionPC 3685 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3685 _ (by rfl)
    _ = 4859 := by rw [fixedPC4008]; rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3687 = 4862 := by
  calc
    Artifact.submissionArtifact.instructionPC 3687 =
        Artifact.submissionArtifact.instructionPC 3686 + (YulEvmCompiler.Instr.push 2 3168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3686 _ (by rfl)
    _ = 4862 := by rw [fixedPC4009]; rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3688 = 4863 := by
  calc
    Artifact.submissionArtifact.instructionPC 3688 =
        Artifact.submissionArtifact.instructionPC 3687 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3687 _ (by rfl)
    _ = 4863 := by rw [fixedPC4010]; rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3689 = 4866 := by
  calc
    Artifact.submissionArtifact.instructionPC 3689 =
        Artifact.submissionArtifact.instructionPC 3688 + (YulEvmCompiler.Instr.push 2 5153).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3688 _ (by rfl)
    _ = 4866 := by rw [fixedPC4011]; rfl


@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2825 = 3776 := by rfl
@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3662 = 4824 := by rfl
@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3663 = 4825 := by rfl
@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3664 = 4826 := by rfl
@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3665 = 4827 := by rfl
@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3666 = 4830 := by rfl
@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3667 = 4831 := by rfl
@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3668 = 4832 := by rfl
@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3669 = 4835 := by rfl
@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3670 = 4836 := by rfl
@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3671 = 4837 := by rfl
@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3672 = 4838 := by rfl
@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3673 = 4841 := by rfl
@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3674 = 4842 := by rfl
@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3675 = 4845 := by rfl
@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3676 = 4846 := by rfl
@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3677 = 4847 := by rfl
@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3678 = 4850 := by rfl
@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3679 = 4851 := by rfl
@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3680 = 4853 := by rfl
@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3681 = 4854 := by rfl
@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3682 = 4855 := by rfl
@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3683 = 4856 := by rfl
@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3684 = 4857 := by rfl
@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3685 = 4858 := by rfl
@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3686 = 4859 := by rfl
@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3687 = 4862 := by rfl
@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3688 = 4863 := by rfl
@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3689 = 4866 := by rfl
@[simp] theorem earlyExtraPC3918 : Artifact.submissionArtifact.instructionPC 3961 = 5231 := by rfl
@[simp] theorem earlyExtraPC3919 : Artifact.submissionArtifact.instructionPC 3962 = 5232 := by rfl
@[simp] theorem earlyExtraPC3920 : Artifact.submissionArtifact.instructionPC 3963 = 5235 := by rfl
@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 3964 = 5236 := by rfl
@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 3965 = 5237 := by rfl
@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 3966 = 5240 := by rfl
@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 3967 = 5243 := by rfl
@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 3968 = 5244 := by rfl
@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 3969 = 5245 := by rfl
@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 3970 = 5246 := by rfl
@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 3971 = 5247 := by rfl
end Challenge.Modexp.Submission.Proofs.Fast
