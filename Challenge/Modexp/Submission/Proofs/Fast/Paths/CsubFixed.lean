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
   pushAt 1618 2 4976,
   opAt 1619 .JUMP,
   opAt 3775 .JUMPDEST,
   pushAt 3776 2 9344,
   opAt 3777 .MLOAD,
   pushAt 3778 2 256,
   opAt 3779 .EQ,
   pushAt 3780 2 5024,
   opAt 3781 .JUMPI,
   pushAt 3782 2 9344,
   opAt 3783 .MLOAD,
   pushAt 3784 1 128,
   opAt 3785 .EQ,
   pushAt 3786 2 5281,
   opAt 3787 .JUMPI,
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
   pushAt 1618 2 4976,
   opAt 1619 .JUMP,
   opAt 3775 .JUMPDEST,
   pushAt 3776 2 9344,
   opAt 3777 .MLOAD,
   pushAt 3778 2 256,
   opAt 3779 .EQ,
   pushAt 3780 2 5024,
   opAt 3781 .JUMPI,
   opAt 3802 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1617 .JUMPDEST,
   pushAt 1618 2 4976,
   opAt 1619 .JUMP,
   opAt 3775 .JUMPDEST,
   pushAt 3776 2 9344,
   opAt 3777 .MLOAD,
   pushAt 3778 2 256,
   opAt 3779 .EQ,
   pushAt 3780 2 5024,
   opAt 3781 .JUMPI,
   pushAt 3782 2 9344,
   opAt 3783 .MLOAD,
   pushAt 3784 1 128,
   opAt 3785 .EQ,
   pushAt 3786 2 5281,
   opAt 3787 .JUMPI,
   opAt 3997 .JUMPDEST]

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
   pushAt 3812 2 7392,
   opAt 3813 .MSTORE]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3814 2 8448,
   opAt 3815 .MLOAD,
   pushAt 3816 1 192,
   opAt 3817 .MLOAD,
   opAt 3818 (.Dup ⟨1, by decide⟩),
   opAt 3819 (.Dup ⟨1, by decide⟩),
   opAt 3820 .GT,
   opAt 3821 (.Swap ⟨1, by decide⟩),
   opAt 3822 .SUB,
   opAt 3823 (.Dup ⟨2, by decide⟩),
   opAt 3824 (.Dup ⟨1, by decide⟩),
   opAt 3825 .SUB,
   opAt 3826 (.Swap ⟨2, by decide⟩),
   opAt 3827 .GT,
   opAt 3828 .OR,
   opAt 3829 (.Swap ⟨0, by decide⟩),
   pushAt 3830 2 7360,
   opAt 3831 .MSTORE]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3832 2 8416,
   opAt 3833 .MLOAD,
   pushAt 3834 1 160,
   opAt 3835 .MLOAD,
   opAt 3836 (.Dup ⟨1, by decide⟩),
   opAt 3837 (.Dup ⟨1, by decide⟩),
   opAt 3838 .GT,
   opAt 3839 (.Swap ⟨1, by decide⟩),
   opAt 3840 .SUB,
   opAt 3841 (.Dup ⟨2, by decide⟩),
   opAt 3842 (.Dup ⟨1, by decide⟩),
   opAt 3843 .SUB,
   opAt 3844 (.Swap ⟨2, by decide⟩),
   opAt 3845 .GT,
   opAt 3846 .OR,
   opAt 3847 (.Swap ⟨0, by decide⟩),
   pushAt 3848 2 7328,
   opAt 3849 .MSTORE]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3850 2 8384,
   opAt 3851 .MLOAD,
   pushAt 3852 1 128,
   opAt 3853 .MLOAD,
   opAt 3854 (.Dup ⟨1, by decide⟩),
   opAt 3855 (.Dup ⟨1, by decide⟩),
   opAt 3856 .GT,
   opAt 3857 (.Swap ⟨1, by decide⟩),
   opAt 3858 .SUB,
   opAt 3859 (.Dup ⟨2, by decide⟩),
   opAt 3860 (.Dup ⟨1, by decide⟩),
   opAt 3861 .SUB,
   opAt 3862 (.Swap ⟨2, by decide⟩),
   opAt 3863 .GT,
   opAt 3864 .OR,
   opAt 3865 (.Swap ⟨0, by decide⟩),
   pushAt 3866 2 7296,
   opAt 3867 .MSTORE]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3868 .JUMPDEST,
   pushAt 3869 2 8352,
   opAt 3870 .MLOAD,
   pushAt 3871 1 96,
   opAt 3872 .MLOAD,
   opAt 3873 (.Dup ⟨1, by decide⟩),
   opAt 3874 (.Dup ⟨1, by decide⟩),
   opAt 3875 .GT,
   opAt 3876 (.Swap ⟨1, by decide⟩),
   opAt 3877 .SUB,
   opAt 3878 (.Dup ⟨2, by decide⟩),
   opAt 3879 (.Dup ⟨1, by decide⟩),
   opAt 3880 .SUB,
   opAt 3881 (.Swap ⟨2, by decide⟩),
   opAt 3882 .GT,
   opAt 3883 .OR,
   opAt 3884 (.Swap ⟨0, by decide⟩),
   pushAt 3885 2 7264,
   opAt 3886 .MSTORE]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3887 .JUMPDEST,
   pushAt 3888 2 8320,
   opAt 3889 .MLOAD,
   pushAt 3890 1 64,
   opAt 3891 .MLOAD,
   opAt 3892 (.Dup ⟨1, by decide⟩),
   opAt 3893 (.Dup ⟨1, by decide⟩),
   opAt 3894 .GT,
   opAt 3895 (.Swap ⟨1, by decide⟩),
   opAt 3896 .SUB,
   opAt 3897 (.Dup ⟨2, by decide⟩),
   opAt 3898 (.Dup ⟨1, by decide⟩),
   opAt 3899 .SUB,
   opAt 3900 (.Swap ⟨2, by decide⟩),
   opAt 3901 .GT,
   opAt 3902 .OR,
   opAt 3903 (.Swap ⟨0, by decide⟩),
   pushAt 3904 2 7232,
   opAt 3905 .MSTORE]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3906 2 8288,
   opAt 3907 .MLOAD,
   pushAt 3908 1 32,
   opAt 3909 .MLOAD,
   opAt 3910 (.Dup ⟨1, by decide⟩),
   opAt 3911 (.Dup ⟨1, by decide⟩),
   opAt 3912 .GT,
   opAt 3913 (.Swap ⟨1, by decide⟩),
   opAt 3914 .SUB,
   opAt 3915 (.Dup ⟨2, by decide⟩),
   opAt 3916 (.Dup ⟨1, by decide⟩),
   opAt 3917 .SUB,
   opAt 3918 (.Swap ⟨2, by decide⟩),
   opAt 3919 .GT,
   opAt 3920 .OR,
   opAt 3921 (.Swap ⟨0, by decide⟩),
   pushAt 3922 2 7200,
   opAt 3923 .MSTORE]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3924 2 8256,
   opAt 3925 .MLOAD,
   pushAt 3926 0 0,
   opAt 3927 .MLOAD,
   opAt 3928 (.Dup ⟨1, by decide⟩),
   opAt 3929 (.Dup ⟨1, by decide⟩),
   opAt 3930 .GT,
   opAt 3931 (.Swap ⟨1, by decide⟩),
   opAt 3932 .SUB,
   opAt 3933 (.Dup ⟨2, by decide⟩),
   opAt 3934 (.Dup ⟨1, by decide⟩),
   opAt 3935 .SUB,
   opAt 3936 (.Swap ⟨2, by decide⟩),
   opAt 3937 .GT,
   opAt 3938 .OR,
   opAt 3939 (.Swap ⟨0, by decide⟩),
   pushAt 3940 2 7168,
   opAt 3941 .MSTORE]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3942 .ISZERO,
   pushAt 3943 2 8224,
   opAt 3944 .MLOAD,
   opAt 3945 .OR,
   pushAt 3946 2 1087,
   opAt 3947 .NOT,
   opAt 3948 .MUL,
   pushAt 3949 2 8256,
   opAt 3950 .ADD,
   pushAt 3951 2 9344,
   opAt 3952 .MLOAD,
   opAt 3953 (.Swap ⟨1, by decide⟩),
   opAt 3954 .MCOPY,
   opAt 3955 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3998 2 8352,
   opAt 3999 .MLOAD,
   pushAt 4000 1 96,
   opAt 4001 .MLOAD,
   opAt 4002 (.Dup ⟨1, by decide⟩),
   opAt 4003 (.Dup ⟨1, by decide⟩),
   opAt 4004 .GT,
   opAt 4005 (.Swap ⟨1, by decide⟩),
   opAt 4006 .SUB,
   pushAt 4007 2 7264,
   opAt 4008 .MSTORE,
   pushAt 4009 2 5134,
   opAt 4010 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3887 .JUMPDEST,
   pushAt 3888 2 8320,
   opAt 3889 .MLOAD,
   pushAt 3890 1 64,
   opAt 3891 .MLOAD,
   opAt 3892 (.Dup ⟨1, by decide⟩),
   opAt 3893 (.Dup ⟨1, by decide⟩),
   opAt 3894 .GT,
   opAt 3895 (.Swap ⟨1, by decide⟩),
   opAt 3896 .SUB,
   opAt 3897 (.Dup ⟨2, by decide⟩),
   opAt 3898 (.Dup ⟨1, by decide⟩),
   opAt 3899 .SUB,
   opAt 3900 (.Swap ⟨2, by decide⟩),
   opAt 3901 .GT,
   opAt 3902 .OR,
   opAt 3903 (.Swap ⟨0, by decide⟩),
   pushAt 3904 2 7232,
   opAt 3905 .MSTORE]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3906 2 8288,
   opAt 3907 .MLOAD,
   pushAt 3908 1 32,
   opAt 3909 .MLOAD,
   opAt 3910 (.Dup ⟨1, by decide⟩),
   opAt 3911 (.Dup ⟨1, by decide⟩),
   opAt 3912 .GT,
   opAt 3913 (.Swap ⟨1, by decide⟩),
   opAt 3914 .SUB,
   opAt 3915 (.Dup ⟨2, by decide⟩),
   opAt 3916 (.Dup ⟨1, by decide⟩),
   opAt 3917 .SUB,
   opAt 3918 (.Swap ⟨2, by decide⟩),
   opAt 3919 .GT,
   opAt 3920 .OR,
   opAt 3921 (.Swap ⟨0, by decide⟩),
   pushAt 3922 2 7200,
   opAt 3923 .MSTORE]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3924 2 8256,
   opAt 3925 .MLOAD,
   pushAt 3926 0 0,
   opAt 3927 .MLOAD,
   opAt 3928 (.Dup ⟨1, by decide⟩),
   opAt 3929 (.Dup ⟨1, by decide⟩),
   opAt 3930 .GT,
   opAt 3931 (.Swap ⟨1, by decide⟩),
   opAt 3932 .SUB,
   opAt 3933 (.Dup ⟨2, by decide⟩),
   opAt 3934 (.Dup ⟨1, by decide⟩),
   opAt 3935 .SUB,
   opAt 3936 (.Swap ⟨2, by decide⟩),
   opAt 3937 .GT,
   opAt 3938 .OR,
   opAt 3939 (.Swap ⟨0, by decide⟩),
   pushAt 3940 2 7168,
   opAt 3941 .MSTORE]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3942 .ISZERO,
   pushAt 3943 2 8224,
   opAt 3944 .MLOAD,
   opAt 3945 .OR,
   pushAt 3946 2 1087,
   opAt 3947 .NOT,
   opAt 3948 .MUL,
   pushAt 3949 2 8256,
   opAt 3950 .ADD,
   pushAt 3951 2 9344,
   opAt 3952 .MLOAD,
   opAt 3953 (.Swap ⟨1, by decide⟩),
   opAt 3954 .MCOPY,
   opAt 3955 .JUMP]

@[simp] theorem fixedPC1617 : Artifact.submissionArtifact.instructionPC 1617 = 2220 := by rfl

@[simp] theorem fixedJump2220 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2220 = true := by
  simpa only [Artifact.instructionPC, fixedPC1617] using Artifact.isValidJumpDest_index 1617 (by rfl)

@[simp] theorem fixedPC1618 : Artifact.submissionArtifact.instructionPC 1618 = 2221 := by
  calc
    Artifact.submissionArtifact.instructionPC 1618 =
        Artifact.submissionArtifact.instructionPC 1617 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1617 _ (by rfl)
    _ = 2221 := by rw [fixedPC1617]; rfl

@[simp] theorem fixedPC1619 : Artifact.submissionArtifact.instructionPC 1619 = 2224 := by
  calc
    Artifact.submissionArtifact.instructionPC 1619 =
        Artifact.submissionArtifact.instructionPC 1618 + (YulEvmCompiler.Instr.push 2 4976).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1618 _ (by rfl)
    _ = 2224 := by rw [fixedPC1618]; rfl

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3775 = 4976 := by rfl

@[simp] theorem fixedJump4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4976 = true := by
  simpa only [Artifact.instructionPC, fixedPC3778] using Artifact.isValidJumpDest_index 3775 (by rfl)

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3776 = 4977 := by
  calc
    Artifact.submissionArtifact.instructionPC 3776 =
        Artifact.submissionArtifact.instructionPC 3775 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3775 _ (by rfl)
    _ = 4977 := by rw [fixedPC3778]; rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3777 = 4980 := by
  calc
    Artifact.submissionArtifact.instructionPC 3777 =
        Artifact.submissionArtifact.instructionPC 3776 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3776 _ (by rfl)
    _ = 4980 := by rw [fixedPC3779]; rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3778 = 4981 := by
  calc
    Artifact.submissionArtifact.instructionPC 3778 =
        Artifact.submissionArtifact.instructionPC 3777 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3777 _ (by rfl)
    _ = 4981 := by rw [fixedPC3780]; rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3779 = 4984 := by
  calc
    Artifact.submissionArtifact.instructionPC 3779 =
        Artifact.submissionArtifact.instructionPC 3778 + (YulEvmCompiler.Instr.push 2 256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3778 _ (by rfl)
    _ = 4984 := by rw [fixedPC3781]; rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3780 = 4985 := by
  calc
    Artifact.submissionArtifact.instructionPC 3780 =
        Artifact.submissionArtifact.instructionPC 3779 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3779 _ (by rfl)
    _ = 4985 := by rw [fixedPC3782]; rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3781 = 4988 := by
  calc
    Artifact.submissionArtifact.instructionPC 3781 =
        Artifact.submissionArtifact.instructionPC 3780 + (YulEvmCompiler.Instr.push 2 5024).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3780 _ (by rfl)
    _ = 4988 := by rw [fixedPC3783]; rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3782 = 4989 := by
  calc
    Artifact.submissionArtifact.instructionPC 3782 =
        Artifact.submissionArtifact.instructionPC 3781 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3781 _ (by rfl)
    _ = 4989 := by rw [fixedPC3784]; rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3783 = 4992 := by
  calc
    Artifact.submissionArtifact.instructionPC 3783 =
        Artifact.submissionArtifact.instructionPC 3782 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3782 _ (by rfl)
    _ = 4992 := by rw [fixedPC3785]; rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3784 = 4993 := by
  calc
    Artifact.submissionArtifact.instructionPC 3784 =
        Artifact.submissionArtifact.instructionPC 3783 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3783 _ (by rfl)
    _ = 4993 := by rw [fixedPC3786]; rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3785 = 4995 := by
  calc
    Artifact.submissionArtifact.instructionPC 3785 =
        Artifact.submissionArtifact.instructionPC 3784 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3784 _ (by rfl)
    _ = 4995 := by rw [fixedPC3787]; rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3786 = 4996 := by
  calc
    Artifact.submissionArtifact.instructionPC 3786 =
        Artifact.submissionArtifact.instructionPC 3785 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3785 _ (by rfl)
    _ = 4996 := by rw [fixedPC3788]; rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3787 = 4999 := by
  calc
    Artifact.submissionArtifact.instructionPC 3787 =
        Artifact.submissionArtifact.instructionPC 3786 + (YulEvmCompiler.Instr.push 2 5281).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3786 _ (by rfl)
    _ = 4999 := by rw [fixedPC3789]; rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3788 = 5000 := by
  calc
    Artifact.submissionArtifact.instructionPC 3788 =
        Artifact.submissionArtifact.instructionPC 3787 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3787 _ (by rfl)
    _ = 5000 := by rw [fixedPC3790]; rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3789 = 5003 := by
  calc
    Artifact.submissionArtifact.instructionPC 3789 =
        Artifact.submissionArtifact.instructionPC 3788 + (YulEvmCompiler.Instr.push 2 9440).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3788 _ (by rfl)
    _ = 5003 := by rw [fixedPC3791]; rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3790 = 5004 := by
  calc
    Artifact.submissionArtifact.instructionPC 3790 =
        Artifact.submissionArtifact.instructionPC 3789 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3789 _ (by rfl)
    _ = 5004 := by rw [fixedPC3792]; rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3791 = 5007 := by
  calc
    Artifact.submissionArtifact.instructionPC 3791 =
        Artifact.submissionArtifact.instructionPC 3790 + (YulEvmCompiler.Instr.push 2 9408).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3790 _ (by rfl)
    _ = 5007 := by rw [fixedPC3793]; rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3792 = 5008 := by
  calc
    Artifact.submissionArtifact.instructionPC 3792 =
        Artifact.submissionArtifact.instructionPC 3791 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3791 _ (by rfl)
    _ = 5008 := by rw [fixedPC3794]; rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3793 = 5009 := by
  calc
    Artifact.submissionArtifact.instructionPC 3793 =
        Artifact.submissionArtifact.instructionPC 3792 + (YulEvmCompiler.Instr.op (.Dup ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3792 _ (by rfl)
    _ = 5009 := by rw [fixedPC3795]; rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3794 = 5012 := by
  calc
    Artifact.submissionArtifact.instructionPC 3794 =
        Artifact.submissionArtifact.instructionPC 3793 + (YulEvmCompiler.Instr.push 2 7168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3793 _ (by rfl)
    _ = 5012 := by rw [fixedPC3796]; rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3795 = 5013 := by
  calc
    Artifact.submissionArtifact.instructionPC 3795 =
        Artifact.submissionArtifact.instructionPC 3794 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3794 _ (by rfl)
    _ = 5013 := by rw [fixedPC3797]; rfl

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3796 = 5016 := by
  calc
    Artifact.submissionArtifact.instructionPC 3796 =
        Artifact.submissionArtifact.instructionPC 3795 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3795 _ (by rfl)
    _ = 5016 := by rw [fixedPC3798]; rfl

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3797 = 5017 := by
  calc
    Artifact.submissionArtifact.instructionPC 3797 =
        Artifact.submissionArtifact.instructionPC 3796 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3796 _ (by rfl)
    _ = 5017 := by rw [fixedPC3799]; rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3798 = 5018 := by
  calc
    Artifact.submissionArtifact.instructionPC 3798 =
        Artifact.submissionArtifact.instructionPC 3797 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3797 _ (by rfl)
    _ = 5018 := by rw [fixedPC3800]; rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3799 = 5019 := by
  calc
    Artifact.submissionArtifact.instructionPC 3799 =
        Artifact.submissionArtifact.instructionPC 3798 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3798 _ (by rfl)
    _ = 5019 := by rw [fixedPC3801]; rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3800 = 5020 := by
  calc
    Artifact.submissionArtifact.instructionPC 3800 =
        Artifact.submissionArtifact.instructionPC 3799 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3799 _ (by rfl)
    _ = 5020 := by rw [fixedPC3802]; rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3801 = 5023 := by
  calc
    Artifact.submissionArtifact.instructionPC 3801 =
        Artifact.submissionArtifact.instructionPC 3800 + (YulEvmCompiler.Instr.push 2 2225).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3800 _ (by rfl)
    _ = 5023 := by rw [fixedPC3803]; rfl

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3802 = 5024 := by
  calc
    Artifact.submissionArtifact.instructionPC 3802 =
        Artifact.submissionArtifact.instructionPC 3801 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3801 _ (by rfl)
    _ = 5024 := by rw [fixedPC3804]; rfl

@[simp] theorem fixedJump5024 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5024 = true := by
  simpa only [Artifact.instructionPC, fixedPC3805] using Artifact.isValidJumpDest_index 3802 (by rfl)

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3803 = 5025 := by
  calc
    Artifact.submissionArtifact.instructionPC 3803 =
        Artifact.submissionArtifact.instructionPC 3802 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3802 _ (by rfl)
    _ = 5025 := by rw [fixedPC3805]; rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3804 = 5028 := by
  calc
    Artifact.submissionArtifact.instructionPC 3804 =
        Artifact.submissionArtifact.instructionPC 3803 + (YulEvmCompiler.Instr.push 2 8480).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3803 _ (by rfl)
    _ = 5028 := by rw [fixedPC3806]; rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3805 = 5029 := by
  calc
    Artifact.submissionArtifact.instructionPC 3805 =
        Artifact.submissionArtifact.instructionPC 3804 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3804 _ (by rfl)
    _ = 5029 := by rw [fixedPC3807]; rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3806 = 5031 := by
  calc
    Artifact.submissionArtifact.instructionPC 3806 =
        Artifact.submissionArtifact.instructionPC 3805 + (YulEvmCompiler.Instr.push 1 224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3805 _ (by rfl)
    _ = 5031 := by rw [fixedPC3808]; rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3807 = 5032 := by
  calc
    Artifact.submissionArtifact.instructionPC 3807 =
        Artifact.submissionArtifact.instructionPC 3806 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3806 _ (by rfl)
    _ = 5032 := by rw [fixedPC3809]; rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3808 = 5033 := by
  calc
    Artifact.submissionArtifact.instructionPC 3808 =
        Artifact.submissionArtifact.instructionPC 3807 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3807 _ (by rfl)
    _ = 5033 := by rw [fixedPC3810]; rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3809 = 5034 := by
  calc
    Artifact.submissionArtifact.instructionPC 3809 =
        Artifact.submissionArtifact.instructionPC 3808 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3808 _ (by rfl)
    _ = 5034 := by rw [fixedPC3811]; rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3810 = 5035 := by
  calc
    Artifact.submissionArtifact.instructionPC 3810 =
        Artifact.submissionArtifact.instructionPC 3809 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3809 _ (by rfl)
    _ = 5035 := by rw [fixedPC3812]; rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3811 = 5036 := by
  calc
    Artifact.submissionArtifact.instructionPC 3811 =
        Artifact.submissionArtifact.instructionPC 3810 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3810 _ (by rfl)
    _ = 5036 := by rw [fixedPC3813]; rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3812 = 5037 := by
  calc
    Artifact.submissionArtifact.instructionPC 3812 =
        Artifact.submissionArtifact.instructionPC 3811 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3811 _ (by rfl)
    _ = 5037 := by rw [fixedPC3814]; rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3813 = 5040 := by
  calc
    Artifact.submissionArtifact.instructionPC 3813 =
        Artifact.submissionArtifact.instructionPC 3812 + (YulEvmCompiler.Instr.push 2 7392).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3812 _ (by rfl)
    _ = 5040 := by rw [fixedPC3815]; rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3814 = 5041 := by
  calc
    Artifact.submissionArtifact.instructionPC 3814 =
        Artifact.submissionArtifact.instructionPC 3813 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3813 _ (by rfl)
    _ = 5041 := by rw [fixedPC3816]; rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3815 = 5044 := by
  calc
    Artifact.submissionArtifact.instructionPC 3815 =
        Artifact.submissionArtifact.instructionPC 3814 + (YulEvmCompiler.Instr.push 2 8448).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3814 _ (by rfl)
    _ = 5044 := by rw [fixedPC3817]; rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3816 = 5045 := by
  calc
    Artifact.submissionArtifact.instructionPC 3816 =
        Artifact.submissionArtifact.instructionPC 3815 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3815 _ (by rfl)
    _ = 5045 := by rw [fixedPC3818]; rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3817 = 5047 := by
  calc
    Artifact.submissionArtifact.instructionPC 3817 =
        Artifact.submissionArtifact.instructionPC 3816 + (YulEvmCompiler.Instr.push 1 192).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3816 _ (by rfl)
    _ = 5047 := by rw [fixedPC3819]; rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3818 = 5048 := by
  calc
    Artifact.submissionArtifact.instructionPC 3818 =
        Artifact.submissionArtifact.instructionPC 3817 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3817 _ (by rfl)
    _ = 5048 := by rw [fixedPC3820]; rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3819 = 5049 := by
  calc
    Artifact.submissionArtifact.instructionPC 3819 =
        Artifact.submissionArtifact.instructionPC 3818 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3818 _ (by rfl)
    _ = 5049 := by rw [fixedPC3821]; rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3820 = 5050 := by
  calc
    Artifact.submissionArtifact.instructionPC 3820 =
        Artifact.submissionArtifact.instructionPC 3819 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3819 _ (by rfl)
    _ = 5050 := by rw [fixedPC3822]; rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3821 = 5051 := by
  calc
    Artifact.submissionArtifact.instructionPC 3821 =
        Artifact.submissionArtifact.instructionPC 3820 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3820 _ (by rfl)
    _ = 5051 := by rw [fixedPC3823]; rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3822 = 5052 := by
  calc
    Artifact.submissionArtifact.instructionPC 3822 =
        Artifact.submissionArtifact.instructionPC 3821 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3821 _ (by rfl)
    _ = 5052 := by rw [fixedPC3824]; rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3823 = 5053 := by
  calc
    Artifact.submissionArtifact.instructionPC 3823 =
        Artifact.submissionArtifact.instructionPC 3822 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3822 _ (by rfl)
    _ = 5053 := by rw [fixedPC3825]; rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3824 = 5054 := by
  calc
    Artifact.submissionArtifact.instructionPC 3824 =
        Artifact.submissionArtifact.instructionPC 3823 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3823 _ (by rfl)
    _ = 5054 := by rw [fixedPC3826]; rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3825 = 5055 := by
  calc
    Artifact.submissionArtifact.instructionPC 3825 =
        Artifact.submissionArtifact.instructionPC 3824 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3824 _ (by rfl)
    _ = 5055 := by rw [fixedPC3827]; rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3826 = 5056 := by
  calc
    Artifact.submissionArtifact.instructionPC 3826 =
        Artifact.submissionArtifact.instructionPC 3825 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3825 _ (by rfl)
    _ = 5056 := by rw [fixedPC3828]; rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3827 = 5057 := by
  calc
    Artifact.submissionArtifact.instructionPC 3827 =
        Artifact.submissionArtifact.instructionPC 3826 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3826 _ (by rfl)
    _ = 5057 := by rw [fixedPC3829]; rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3828 = 5058 := by
  calc
    Artifact.submissionArtifact.instructionPC 3828 =
        Artifact.submissionArtifact.instructionPC 3827 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3827 _ (by rfl)
    _ = 5058 := by rw [fixedPC3830]; rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3829 = 5059 := by
  calc
    Artifact.submissionArtifact.instructionPC 3829 =
        Artifact.submissionArtifact.instructionPC 3828 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3828 _ (by rfl)
    _ = 5059 := by rw [fixedPC3831]; rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3830 = 5060 := by
  calc
    Artifact.submissionArtifact.instructionPC 3830 =
        Artifact.submissionArtifact.instructionPC 3829 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3829 _ (by rfl)
    _ = 5060 := by rw [fixedPC3832]; rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3831 = 5063 := by
  calc
    Artifact.submissionArtifact.instructionPC 3831 =
        Artifact.submissionArtifact.instructionPC 3830 + (YulEvmCompiler.Instr.push 2 7360).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3830 _ (by rfl)
    _ = 5063 := by rw [fixedPC3833]; rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3832 = 5064 := by
  calc
    Artifact.submissionArtifact.instructionPC 3832 =
        Artifact.submissionArtifact.instructionPC 3831 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3831 _ (by rfl)
    _ = 5064 := by rw [fixedPC3834]; rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3833 = 5067 := by
  calc
    Artifact.submissionArtifact.instructionPC 3833 =
        Artifact.submissionArtifact.instructionPC 3832 + (YulEvmCompiler.Instr.push 2 8416).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3832 _ (by rfl)
    _ = 5067 := by rw [fixedPC3835]; rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3834 = 5068 := by
  calc
    Artifact.submissionArtifact.instructionPC 3834 =
        Artifact.submissionArtifact.instructionPC 3833 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3833 _ (by rfl)
    _ = 5068 := by rw [fixedPC3836]; rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3835 = 5070 := by
  calc
    Artifact.submissionArtifact.instructionPC 3835 =
        Artifact.submissionArtifact.instructionPC 3834 + (YulEvmCompiler.Instr.push 1 160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3834 _ (by rfl)
    _ = 5070 := by rw [fixedPC3837]; rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3836 = 5071 := by
  calc
    Artifact.submissionArtifact.instructionPC 3836 =
        Artifact.submissionArtifact.instructionPC 3835 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3835 _ (by rfl)
    _ = 5071 := by rw [fixedPC3838]; rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3837 = 5072 := by
  calc
    Artifact.submissionArtifact.instructionPC 3837 =
        Artifact.submissionArtifact.instructionPC 3836 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3836 _ (by rfl)
    _ = 5072 := by rw [fixedPC3839]; rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3838 = 5073 := by
  calc
    Artifact.submissionArtifact.instructionPC 3838 =
        Artifact.submissionArtifact.instructionPC 3837 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3837 _ (by rfl)
    _ = 5073 := by rw [fixedPC3840]; rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3839 = 5074 := by
  calc
    Artifact.submissionArtifact.instructionPC 3839 =
        Artifact.submissionArtifact.instructionPC 3838 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3838 _ (by rfl)
    _ = 5074 := by rw [fixedPC3841]; rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3840 = 5075 := by
  calc
    Artifact.submissionArtifact.instructionPC 3840 =
        Artifact.submissionArtifact.instructionPC 3839 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3839 _ (by rfl)
    _ = 5075 := by rw [fixedPC3842]; rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3841 = 5076 := by
  calc
    Artifact.submissionArtifact.instructionPC 3841 =
        Artifact.submissionArtifact.instructionPC 3840 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3840 _ (by rfl)
    _ = 5076 := by rw [fixedPC3843]; rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3842 = 5077 := by
  calc
    Artifact.submissionArtifact.instructionPC 3842 =
        Artifact.submissionArtifact.instructionPC 3841 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3841 _ (by rfl)
    _ = 5077 := by rw [fixedPC3844]; rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3843 = 5078 := by
  calc
    Artifact.submissionArtifact.instructionPC 3843 =
        Artifact.submissionArtifact.instructionPC 3842 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3842 _ (by rfl)
    _ = 5078 := by rw [fixedPC3845]; rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3844 = 5079 := by
  calc
    Artifact.submissionArtifact.instructionPC 3844 =
        Artifact.submissionArtifact.instructionPC 3843 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3843 _ (by rfl)
    _ = 5079 := by rw [fixedPC3846]; rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3845 = 5080 := by
  calc
    Artifact.submissionArtifact.instructionPC 3845 =
        Artifact.submissionArtifact.instructionPC 3844 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3844 _ (by rfl)
    _ = 5080 := by rw [fixedPC3847]; rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3846 = 5081 := by
  calc
    Artifact.submissionArtifact.instructionPC 3846 =
        Artifact.submissionArtifact.instructionPC 3845 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3845 _ (by rfl)
    _ = 5081 := by rw [fixedPC3848]; rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3847 = 5082 := by
  calc
    Artifact.submissionArtifact.instructionPC 3847 =
        Artifact.submissionArtifact.instructionPC 3846 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3846 _ (by rfl)
    _ = 5082 := by rw [fixedPC3849]; rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3848 = 5083 := by
  calc
    Artifact.submissionArtifact.instructionPC 3848 =
        Artifact.submissionArtifact.instructionPC 3847 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3847 _ (by rfl)
    _ = 5083 := by rw [fixedPC3850]; rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3849 = 5086 := by
  calc
    Artifact.submissionArtifact.instructionPC 3849 =
        Artifact.submissionArtifact.instructionPC 3848 + (YulEvmCompiler.Instr.push 2 7328).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3848 _ (by rfl)
    _ = 5086 := by rw [fixedPC3851]; rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3850 = 5087 := by
  calc
    Artifact.submissionArtifact.instructionPC 3850 =
        Artifact.submissionArtifact.instructionPC 3849 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3849 _ (by rfl)
    _ = 5087 := by rw [fixedPC3852]; rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3851 = 5090 := by
  calc
    Artifact.submissionArtifact.instructionPC 3851 =
        Artifact.submissionArtifact.instructionPC 3850 + (YulEvmCompiler.Instr.push 2 8384).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3850 _ (by rfl)
    _ = 5090 := by rw [fixedPC3853]; rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3852 = 5091 := by
  calc
    Artifact.submissionArtifact.instructionPC 3852 =
        Artifact.submissionArtifact.instructionPC 3851 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3851 _ (by rfl)
    _ = 5091 := by rw [fixedPC3854]; rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3853 = 5093 := by
  calc
    Artifact.submissionArtifact.instructionPC 3853 =
        Artifact.submissionArtifact.instructionPC 3852 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3852 _ (by rfl)
    _ = 5093 := by rw [fixedPC3855]; rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3854 = 5094 := by
  calc
    Artifact.submissionArtifact.instructionPC 3854 =
        Artifact.submissionArtifact.instructionPC 3853 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3853 _ (by rfl)
    _ = 5094 := by rw [fixedPC3856]; rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3855 = 5095 := by
  calc
    Artifact.submissionArtifact.instructionPC 3855 =
        Artifact.submissionArtifact.instructionPC 3854 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3854 _ (by rfl)
    _ = 5095 := by rw [fixedPC3857]; rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3856 = 5096 := by
  calc
    Artifact.submissionArtifact.instructionPC 3856 =
        Artifact.submissionArtifact.instructionPC 3855 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3855 _ (by rfl)
    _ = 5096 := by rw [fixedPC3858]; rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3857 = 5097 := by
  calc
    Artifact.submissionArtifact.instructionPC 3857 =
        Artifact.submissionArtifact.instructionPC 3856 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3856 _ (by rfl)
    _ = 5097 := by rw [fixedPC3859]; rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3858 = 5098 := by
  calc
    Artifact.submissionArtifact.instructionPC 3858 =
        Artifact.submissionArtifact.instructionPC 3857 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3857 _ (by rfl)
    _ = 5098 := by rw [fixedPC3860]; rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3859 = 5099 := by
  calc
    Artifact.submissionArtifact.instructionPC 3859 =
        Artifact.submissionArtifact.instructionPC 3858 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3858 _ (by rfl)
    _ = 5099 := by rw [fixedPC3861]; rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3860 = 5100 := by
  calc
    Artifact.submissionArtifact.instructionPC 3860 =
        Artifact.submissionArtifact.instructionPC 3859 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3859 _ (by rfl)
    _ = 5100 := by rw [fixedPC3862]; rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3861 = 5101 := by
  calc
    Artifact.submissionArtifact.instructionPC 3861 =
        Artifact.submissionArtifact.instructionPC 3860 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3860 _ (by rfl)
    _ = 5101 := by rw [fixedPC3863]; rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3862 = 5102 := by
  calc
    Artifact.submissionArtifact.instructionPC 3862 =
        Artifact.submissionArtifact.instructionPC 3861 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3861 _ (by rfl)
    _ = 5102 := by rw [fixedPC3864]; rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3863 = 5103 := by
  calc
    Artifact.submissionArtifact.instructionPC 3863 =
        Artifact.submissionArtifact.instructionPC 3862 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3862 _ (by rfl)
    _ = 5103 := by rw [fixedPC3865]; rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3864 = 5104 := by
  calc
    Artifact.submissionArtifact.instructionPC 3864 =
        Artifact.submissionArtifact.instructionPC 3863 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3863 _ (by rfl)
    _ = 5104 := by rw [fixedPC3866]; rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3865 = 5105 := by
  calc
    Artifact.submissionArtifact.instructionPC 3865 =
        Artifact.submissionArtifact.instructionPC 3864 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3864 _ (by rfl)
    _ = 5105 := by rw [fixedPC3867]; rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3866 = 5106 := by
  calc
    Artifact.submissionArtifact.instructionPC 3866 =
        Artifact.submissionArtifact.instructionPC 3865 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3865 _ (by rfl)
    _ = 5106 := by rw [fixedPC3868]; rfl

@[simp] theorem fixedPC3870 : Artifact.submissionArtifact.instructionPC 3867 = 5109 := by
  calc
    Artifact.submissionArtifact.instructionPC 3867 =
        Artifact.submissionArtifact.instructionPC 3866 + (YulEvmCompiler.Instr.push 2 7296).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3866 _ (by rfl)
    _ = 5109 := by rw [fixedPC3869]; rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3868 = 5110 := by
  calc
    Artifact.submissionArtifact.instructionPC 3868 =
        Artifact.submissionArtifact.instructionPC 3867 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3867 _ (by rfl)
    _ = 5110 := by rw [fixedPC3870]; rfl

@[simp] theorem fixedJump5110 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5110 = true := by
  simpa only [Artifact.instructionPC, fixedPC3871] using Artifact.isValidJumpDest_index 3868 (by rfl)

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3869 = 5111 := by
  calc
    Artifact.submissionArtifact.instructionPC 3869 =
        Artifact.submissionArtifact.instructionPC 3868 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3868 _ (by rfl)
    _ = 5111 := by rw [fixedPC3871]; rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3870 = 5114 := by
  calc
    Artifact.submissionArtifact.instructionPC 3870 =
        Artifact.submissionArtifact.instructionPC 3869 + (YulEvmCompiler.Instr.push 2 8352).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3869 _ (by rfl)
    _ = 5114 := by rw [fixedPC3872]; rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3871 = 5115 := by
  calc
    Artifact.submissionArtifact.instructionPC 3871 =
        Artifact.submissionArtifact.instructionPC 3870 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3870 _ (by rfl)
    _ = 5115 := by rw [fixedPC3873]; rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3872 = 5117 := by
  calc
    Artifact.submissionArtifact.instructionPC 3872 =
        Artifact.submissionArtifact.instructionPC 3871 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3871 _ (by rfl)
    _ = 5117 := by rw [fixedPC3874]; rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3873 = 5118 := by
  calc
    Artifact.submissionArtifact.instructionPC 3873 =
        Artifact.submissionArtifact.instructionPC 3872 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3872 _ (by rfl)
    _ = 5118 := by rw [fixedPC3875]; rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3874 = 5119 := by
  calc
    Artifact.submissionArtifact.instructionPC 3874 =
        Artifact.submissionArtifact.instructionPC 3873 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3873 _ (by rfl)
    _ = 5119 := by rw [fixedPC3876]; rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3875 = 5120 := by
  calc
    Artifact.submissionArtifact.instructionPC 3875 =
        Artifact.submissionArtifact.instructionPC 3874 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3874 _ (by rfl)
    _ = 5120 := by rw [fixedPC3877]; rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3876 = 5121 := by
  calc
    Artifact.submissionArtifact.instructionPC 3876 =
        Artifact.submissionArtifact.instructionPC 3875 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3875 _ (by rfl)
    _ = 5121 := by rw [fixedPC3878]; rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3877 = 5122 := by
  calc
    Artifact.submissionArtifact.instructionPC 3877 =
        Artifact.submissionArtifact.instructionPC 3876 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3876 _ (by rfl)
    _ = 5122 := by rw [fixedPC3879]; rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3878 = 5123 := by
  calc
    Artifact.submissionArtifact.instructionPC 3878 =
        Artifact.submissionArtifact.instructionPC 3877 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3877 _ (by rfl)
    _ = 5123 := by rw [fixedPC3880]; rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3879 = 5124 := by
  calc
    Artifact.submissionArtifact.instructionPC 3879 =
        Artifact.submissionArtifact.instructionPC 3878 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3878 _ (by rfl)
    _ = 5124 := by rw [fixedPC3881]; rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3880 = 5125 := by
  calc
    Artifact.submissionArtifact.instructionPC 3880 =
        Artifact.submissionArtifact.instructionPC 3879 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3879 _ (by rfl)
    _ = 5125 := by rw [fixedPC3882]; rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3881 = 5126 := by
  calc
    Artifact.submissionArtifact.instructionPC 3881 =
        Artifact.submissionArtifact.instructionPC 3880 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3880 _ (by rfl)
    _ = 5126 := by rw [fixedPC3883]; rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3882 = 5127 := by
  calc
    Artifact.submissionArtifact.instructionPC 3882 =
        Artifact.submissionArtifact.instructionPC 3881 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3881 _ (by rfl)
    _ = 5127 := by rw [fixedPC3884]; rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3883 = 5128 := by
  calc
    Artifact.submissionArtifact.instructionPC 3883 =
        Artifact.submissionArtifact.instructionPC 3882 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3882 _ (by rfl)
    _ = 5128 := by rw [fixedPC3885]; rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3884 = 5129 := by
  calc
    Artifact.submissionArtifact.instructionPC 3884 =
        Artifact.submissionArtifact.instructionPC 3883 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3883 _ (by rfl)
    _ = 5129 := by rw [fixedPC3886]; rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3885 = 5130 := by
  calc
    Artifact.submissionArtifact.instructionPC 3885 =
        Artifact.submissionArtifact.instructionPC 3884 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3884 _ (by rfl)
    _ = 5130 := by rw [fixedPC3887]; rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3886 = 5133 := by
  calc
    Artifact.submissionArtifact.instructionPC 3886 =
        Artifact.submissionArtifact.instructionPC 3885 + (YulEvmCompiler.Instr.push 2 7264).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3885 _ (by rfl)
    _ = 5133 := by rw [fixedPC3888]; rfl

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3887 = 5134 := by
  calc
    Artifact.submissionArtifact.instructionPC 3887 =
        Artifact.submissionArtifact.instructionPC 3886 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3886 _ (by rfl)
    _ = 5134 := by rw [fixedPC3889]; rfl

@[simp] theorem fixedJump5134 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5134 = true := by
  simpa only [Artifact.instructionPC, fixedPC3890] using Artifact.isValidJumpDest_index 3887 (by rfl)

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3888 = 5135 := by
  calc
    Artifact.submissionArtifact.instructionPC 3888 =
        Artifact.submissionArtifact.instructionPC 3887 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3887 _ (by rfl)
    _ = 5135 := by rw [fixedPC3890]; rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3889 = 5138 := by
  calc
    Artifact.submissionArtifact.instructionPC 3889 =
        Artifact.submissionArtifact.instructionPC 3888 + (YulEvmCompiler.Instr.push 2 8320).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3888 _ (by rfl)
    _ = 5138 := by rw [fixedPC3891]; rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3890 = 5139 := by
  calc
    Artifact.submissionArtifact.instructionPC 3890 =
        Artifact.submissionArtifact.instructionPC 3889 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3889 _ (by rfl)
    _ = 5139 := by rw [fixedPC3892]; rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3891 = 5141 := by
  calc
    Artifact.submissionArtifact.instructionPC 3891 =
        Artifact.submissionArtifact.instructionPC 3890 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3890 _ (by rfl)
    _ = 5141 := by rw [fixedPC3893]; rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3892 = 5142 := by
  calc
    Artifact.submissionArtifact.instructionPC 3892 =
        Artifact.submissionArtifact.instructionPC 3891 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3891 _ (by rfl)
    _ = 5142 := by rw [fixedPC3894]; rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3893 = 5143 := by
  calc
    Artifact.submissionArtifact.instructionPC 3893 =
        Artifact.submissionArtifact.instructionPC 3892 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3892 _ (by rfl)
    _ = 5143 := by rw [fixedPC3895]; rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3894 = 5144 := by
  calc
    Artifact.submissionArtifact.instructionPC 3894 =
        Artifact.submissionArtifact.instructionPC 3893 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3893 _ (by rfl)
    _ = 5144 := by rw [fixedPC3896]; rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3895 = 5145 := by
  calc
    Artifact.submissionArtifact.instructionPC 3895 =
        Artifact.submissionArtifact.instructionPC 3894 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3894 _ (by rfl)
    _ = 5145 := by rw [fixedPC3897]; rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3896 = 5146 := by
  calc
    Artifact.submissionArtifact.instructionPC 3896 =
        Artifact.submissionArtifact.instructionPC 3895 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3895 _ (by rfl)
    _ = 5146 := by rw [fixedPC3898]; rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3897 = 5147 := by
  calc
    Artifact.submissionArtifact.instructionPC 3897 =
        Artifact.submissionArtifact.instructionPC 3896 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3896 _ (by rfl)
    _ = 5147 := by rw [fixedPC3899]; rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3898 = 5148 := by
  calc
    Artifact.submissionArtifact.instructionPC 3898 =
        Artifact.submissionArtifact.instructionPC 3897 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3897 _ (by rfl)
    _ = 5148 := by rw [fixedPC3900]; rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3899 = 5149 := by
  calc
    Artifact.submissionArtifact.instructionPC 3899 =
        Artifact.submissionArtifact.instructionPC 3898 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3898 _ (by rfl)
    _ = 5149 := by rw [fixedPC3901]; rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3900 = 5150 := by
  calc
    Artifact.submissionArtifact.instructionPC 3900 =
        Artifact.submissionArtifact.instructionPC 3899 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3899 _ (by rfl)
    _ = 5150 := by rw [fixedPC3902]; rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3901 = 5151 := by
  calc
    Artifact.submissionArtifact.instructionPC 3901 =
        Artifact.submissionArtifact.instructionPC 3900 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3900 _ (by rfl)
    _ = 5151 := by rw [fixedPC3903]; rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3902 = 5152 := by
  calc
    Artifact.submissionArtifact.instructionPC 3902 =
        Artifact.submissionArtifact.instructionPC 3901 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3901 _ (by rfl)
    _ = 5152 := by rw [fixedPC3904]; rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3903 = 5153 := by
  calc
    Artifact.submissionArtifact.instructionPC 3903 =
        Artifact.submissionArtifact.instructionPC 3902 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3902 _ (by rfl)
    _ = 5153 := by rw [fixedPC3905]; rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3904 = 5154 := by
  calc
    Artifact.submissionArtifact.instructionPC 3904 =
        Artifact.submissionArtifact.instructionPC 3903 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3903 _ (by rfl)
    _ = 5154 := by rw [fixedPC3906]; rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3905 = 5157 := by
  calc
    Artifact.submissionArtifact.instructionPC 3905 =
        Artifact.submissionArtifact.instructionPC 3904 + (YulEvmCompiler.Instr.push 2 7232).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3904 _ (by rfl)
    _ = 5157 := by rw [fixedPC3907]; rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3906 = 5158 := by
  calc
    Artifact.submissionArtifact.instructionPC 3906 =
        Artifact.submissionArtifact.instructionPC 3905 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3905 _ (by rfl)
    _ = 5158 := by rw [fixedPC3908]; rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3907 = 5161 := by
  calc
    Artifact.submissionArtifact.instructionPC 3907 =
        Artifact.submissionArtifact.instructionPC 3906 + (YulEvmCompiler.Instr.push 2 8288).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3906 _ (by rfl)
    _ = 5161 := by rw [fixedPC3909]; rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3908 = 5162 := by
  calc
    Artifact.submissionArtifact.instructionPC 3908 =
        Artifact.submissionArtifact.instructionPC 3907 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3907 _ (by rfl)
    _ = 5162 := by rw [fixedPC3910]; rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3909 = 5164 := by
  calc
    Artifact.submissionArtifact.instructionPC 3909 =
        Artifact.submissionArtifact.instructionPC 3908 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3908 _ (by rfl)
    _ = 5164 := by rw [fixedPC3911]; rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3910 = 5165 := by
  calc
    Artifact.submissionArtifact.instructionPC 3910 =
        Artifact.submissionArtifact.instructionPC 3909 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3909 _ (by rfl)
    _ = 5165 := by rw [fixedPC3912]; rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3911 = 5166 := by
  calc
    Artifact.submissionArtifact.instructionPC 3911 =
        Artifact.submissionArtifact.instructionPC 3910 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3910 _ (by rfl)
    _ = 5166 := by rw [fixedPC3913]; rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3912 = 5167 := by
  calc
    Artifact.submissionArtifact.instructionPC 3912 =
        Artifact.submissionArtifact.instructionPC 3911 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3911 _ (by rfl)
    _ = 5167 := by rw [fixedPC3914]; rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3913 = 5168 := by
  calc
    Artifact.submissionArtifact.instructionPC 3913 =
        Artifact.submissionArtifact.instructionPC 3912 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3912 _ (by rfl)
    _ = 5168 := by rw [fixedPC3915]; rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3914 = 5169 := by
  calc
    Artifact.submissionArtifact.instructionPC 3914 =
        Artifact.submissionArtifact.instructionPC 3913 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3913 _ (by rfl)
    _ = 5169 := by rw [fixedPC3916]; rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3915 = 5170 := by
  calc
    Artifact.submissionArtifact.instructionPC 3915 =
        Artifact.submissionArtifact.instructionPC 3914 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3914 _ (by rfl)
    _ = 5170 := by rw [fixedPC3917]; rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3916 = 5171 := by
  calc
    Artifact.submissionArtifact.instructionPC 3916 =
        Artifact.submissionArtifact.instructionPC 3915 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3915 _ (by rfl)
    _ = 5171 := by rw [fixedPC3918]; rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3917 = 5172 := by
  calc
    Artifact.submissionArtifact.instructionPC 3917 =
        Artifact.submissionArtifact.instructionPC 3916 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3916 _ (by rfl)
    _ = 5172 := by rw [fixedPC3919]; rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3918 = 5173 := by
  calc
    Artifact.submissionArtifact.instructionPC 3918 =
        Artifact.submissionArtifact.instructionPC 3917 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3917 _ (by rfl)
    _ = 5173 := by rw [fixedPC3920]; rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3919 = 5174 := by
  calc
    Artifact.submissionArtifact.instructionPC 3919 =
        Artifact.submissionArtifact.instructionPC 3918 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3918 _ (by rfl)
    _ = 5174 := by rw [fixedPC3921]; rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3920 = 5175 := by
  calc
    Artifact.submissionArtifact.instructionPC 3920 =
        Artifact.submissionArtifact.instructionPC 3919 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3919 _ (by rfl)
    _ = 5175 := by rw [fixedPC3922]; rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3921 = 5176 := by
  calc
    Artifact.submissionArtifact.instructionPC 3921 =
        Artifact.submissionArtifact.instructionPC 3920 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3920 _ (by rfl)
    _ = 5176 := by rw [fixedPC3923]; rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3922 = 5177 := by
  calc
    Artifact.submissionArtifact.instructionPC 3922 =
        Artifact.submissionArtifact.instructionPC 3921 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3921 _ (by rfl)
    _ = 5177 := by rw [fixedPC3924]; rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3923 = 5180 := by
  calc
    Artifact.submissionArtifact.instructionPC 3923 =
        Artifact.submissionArtifact.instructionPC 3922 + (YulEvmCompiler.Instr.push 2 7200).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3922 _ (by rfl)
    _ = 5180 := by rw [fixedPC3925]; rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3924 = 5181 := by
  calc
    Artifact.submissionArtifact.instructionPC 3924 =
        Artifact.submissionArtifact.instructionPC 3923 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3923 _ (by rfl)
    _ = 5181 := by rw [fixedPC3926]; rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3925 = 5184 := by
  calc
    Artifact.submissionArtifact.instructionPC 3925 =
        Artifact.submissionArtifact.instructionPC 3924 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3924 _ (by rfl)
    _ = 5184 := by rw [fixedPC3927]; rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3926 = 5185 := by
  calc
    Artifact.submissionArtifact.instructionPC 3926 =
        Artifact.submissionArtifact.instructionPC 3925 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3925 _ (by rfl)
    _ = 5185 := by rw [fixedPC3928]; rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3927 = 5186 := by
  calc
    Artifact.submissionArtifact.instructionPC 3927 =
        Artifact.submissionArtifact.instructionPC 3926 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3926 _ (by rfl)
    _ = 5186 := by rw [fixedPC3929]; rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3928 = 5187 := by
  calc
    Artifact.submissionArtifact.instructionPC 3928 =
        Artifact.submissionArtifact.instructionPC 3927 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3927 _ (by rfl)
    _ = 5187 := by rw [fixedPC3930]; rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3929 = 5188 := by
  calc
    Artifact.submissionArtifact.instructionPC 3929 =
        Artifact.submissionArtifact.instructionPC 3928 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3928 _ (by rfl)
    _ = 5188 := by rw [fixedPC3931]; rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3930 = 5189 := by
  calc
    Artifact.submissionArtifact.instructionPC 3930 =
        Artifact.submissionArtifact.instructionPC 3929 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3929 _ (by rfl)
    _ = 5189 := by rw [fixedPC3932]; rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3931 = 5190 := by
  calc
    Artifact.submissionArtifact.instructionPC 3931 =
        Artifact.submissionArtifact.instructionPC 3930 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3930 _ (by rfl)
    _ = 5190 := by rw [fixedPC3933]; rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3932 = 5191 := by
  calc
    Artifact.submissionArtifact.instructionPC 3932 =
        Artifact.submissionArtifact.instructionPC 3931 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3931 _ (by rfl)
    _ = 5191 := by rw [fixedPC3934]; rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3933 = 5192 := by
  calc
    Artifact.submissionArtifact.instructionPC 3933 =
        Artifact.submissionArtifact.instructionPC 3932 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3932 _ (by rfl)
    _ = 5192 := by rw [fixedPC3935]; rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3934 = 5193 := by
  calc
    Artifact.submissionArtifact.instructionPC 3934 =
        Artifact.submissionArtifact.instructionPC 3933 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3933 _ (by rfl)
    _ = 5193 := by rw [fixedPC3936]; rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3935 = 5194 := by
  calc
    Artifact.submissionArtifact.instructionPC 3935 =
        Artifact.submissionArtifact.instructionPC 3934 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3934 _ (by rfl)
    _ = 5194 := by rw [fixedPC3937]; rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3936 = 5195 := by
  calc
    Artifact.submissionArtifact.instructionPC 3936 =
        Artifact.submissionArtifact.instructionPC 3935 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3935 _ (by rfl)
    _ = 5195 := by rw [fixedPC3938]; rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3937 = 5196 := by
  calc
    Artifact.submissionArtifact.instructionPC 3937 =
        Artifact.submissionArtifact.instructionPC 3936 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3936 _ (by rfl)
    _ = 5196 := by rw [fixedPC3939]; rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3938 = 5197 := by
  calc
    Artifact.submissionArtifact.instructionPC 3938 =
        Artifact.submissionArtifact.instructionPC 3937 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3937 _ (by rfl)
    _ = 5197 := by rw [fixedPC3940]; rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3939 = 5198 := by
  calc
    Artifact.submissionArtifact.instructionPC 3939 =
        Artifact.submissionArtifact.instructionPC 3938 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3938 _ (by rfl)
    _ = 5198 := by rw [fixedPC3941]; rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3940 = 5199 := by
  calc
    Artifact.submissionArtifact.instructionPC 3940 =
        Artifact.submissionArtifact.instructionPC 3939 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3939 _ (by rfl)
    _ = 5199 := by rw [fixedPC3942]; rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3941 = 5202 := by
  calc
    Artifact.submissionArtifact.instructionPC 3941 =
        Artifact.submissionArtifact.instructionPC 3940 + (YulEvmCompiler.Instr.push 2 7168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3940 _ (by rfl)
    _ = 5202 := by rw [fixedPC3943]; rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3942 = 5203 := by
  calc
    Artifact.submissionArtifact.instructionPC 3942 =
        Artifact.submissionArtifact.instructionPC 3941 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3941 _ (by rfl)
    _ = 5203 := by rw [fixedPC3944]; rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3943 = 5204 := by
  calc
    Artifact.submissionArtifact.instructionPC 3943 =
        Artifact.submissionArtifact.instructionPC 3942 + (YulEvmCompiler.Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3942 _ (by rfl)
    _ = 5204 := by rw [fixedPC3945]; rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3944 = 5207 := by
  calc
    Artifact.submissionArtifact.instructionPC 3944 =
        Artifact.submissionArtifact.instructionPC 3943 + (YulEvmCompiler.Instr.push 2 8224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3943 _ (by rfl)
    _ = 5207 := by rw [fixedPC3946]; rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3945 = 5208 := by
  calc
    Artifact.submissionArtifact.instructionPC 3945 =
        Artifact.submissionArtifact.instructionPC 3944 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3944 _ (by rfl)
    _ = 5208 := by rw [fixedPC3947]; rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3946 = 5209 := by
  calc
    Artifact.submissionArtifact.instructionPC 3946 =
        Artifact.submissionArtifact.instructionPC 3945 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3945 _ (by rfl)
    _ = 5209 := by rw [fixedPC3948]; rfl

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3947 = 5212 := by
  calc
    Artifact.submissionArtifact.instructionPC 3947 =
        Artifact.submissionArtifact.instructionPC 3946 + (YulEvmCompiler.Instr.push 2 1087).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3946 _ (by rfl)
    _ = 5212 := by rw [fixedPC3949]; rfl

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3948 = 5213 := by
  calc
    Artifact.submissionArtifact.instructionPC 3948 =
        Artifact.submissionArtifact.instructionPC 3947 + (YulEvmCompiler.Instr.op .NOT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3947 _ (by rfl)
    _ = 5213 := by rw [fixedPC3950]; rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3949 = 5214 := by
  calc
    Artifact.submissionArtifact.instructionPC 3949 =
        Artifact.submissionArtifact.instructionPC 3948 + (YulEvmCompiler.Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3948 _ (by rfl)
    _ = 5214 := by rw [fixedPC3951]; rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3950 = 5217 := by
  calc
    Artifact.submissionArtifact.instructionPC 3950 =
        Artifact.submissionArtifact.instructionPC 3949 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3949 _ (by rfl)
    _ = 5217 := by rw [fixedPC3952]; rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3951 = 5218 := by
  calc
    Artifact.submissionArtifact.instructionPC 3951 =
        Artifact.submissionArtifact.instructionPC 3950 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3950 _ (by rfl)
    _ = 5218 := by rw [fixedPC3953]; rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3952 = 5221 := by
  calc
    Artifact.submissionArtifact.instructionPC 3952 =
        Artifact.submissionArtifact.instructionPC 3951 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3951 _ (by rfl)
    _ = 5221 := by rw [fixedPC3954]; rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3953 = 5222 := by
  calc
    Artifact.submissionArtifact.instructionPC 3953 =
        Artifact.submissionArtifact.instructionPC 3952 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3952 _ (by rfl)
    _ = 5222 := by rw [fixedPC3955]; rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3954 = 5223 := by
  calc
    Artifact.submissionArtifact.instructionPC 3954 =
        Artifact.submissionArtifact.instructionPC 3953 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3953 _ (by rfl)
    _ = 5223 := by rw [fixedPC3956]; rfl

@[simp] theorem fixedPC3958 : Artifact.submissionArtifact.instructionPC 3955 = 5224 := by
  calc
    Artifact.submissionArtifact.instructionPC 3955 =
        Artifact.submissionArtifact.instructionPC 3954 + (YulEvmCompiler.Instr.op .MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3954 _ (by rfl)
    _ = 5224 := by rw [fixedPC3957]; rfl

@[simp] theorem fixedPC3959 : Artifact.submissionArtifact.instructionPC 3956 = 5225 := by
  calc
    Artifact.submissionArtifact.instructionPC 3956 =
        Artifact.submissionArtifact.instructionPC 3955 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3955 _ (by rfl)
    _ = 5225 := by rw [fixedPC3958]; rfl

@[simp] theorem fixedJump5225 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5225 = true := by
  simpa only [Artifact.instructionPC, fixedPC3959] using Artifact.isValidJumpDest_index 3956 (by rfl)

@[simp] theorem fixedPC3960 : Artifact.submissionArtifact.instructionPC 3957 = 5226 := by
  calc
    Artifact.submissionArtifact.instructionPC 3957 =
        Artifact.submissionArtifact.instructionPC 3956 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3956 _ (by rfl)
    _ = 5226 := by rw [fixedPC3959]; rfl

@[simp] theorem fixedPC3961 : Artifact.submissionArtifact.instructionPC 3958 = 5227 := by
  calc
    Artifact.submissionArtifact.instructionPC 3958 =
        Artifact.submissionArtifact.instructionPC 3957 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3957 _ (by rfl)
    _ = 5227 := by rw [fixedPC3960]; rfl

@[simp] theorem fixedPC3962 : Artifact.submissionArtifact.instructionPC 3959 = 5228 := by
  calc
    Artifact.submissionArtifact.instructionPC 3959 =
        Artifact.submissionArtifact.instructionPC 3958 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3958 _ (by rfl)
    _ = 5228 := by rw [fixedPC3961]; rfl

@[simp] theorem fixedPC3963 : Artifact.submissionArtifact.instructionPC 3960 = 5230 := by
  calc
    Artifact.submissionArtifact.instructionPC 3960 =
        Artifact.submissionArtifact.instructionPC 3959 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3959 _ (by rfl)
    _ = 5230 := by rw [fixedPC3962]; rfl

@[simp] theorem fixedPC3964 : Artifact.submissionArtifact.instructionPC 3961 = 5231 := by
  calc
    Artifact.submissionArtifact.instructionPC 3961 =
        Artifact.submissionArtifact.instructionPC 3960 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3960 _ (by rfl)
    _ = 5231 := by rw [fixedPC3963]; rfl

@[simp] theorem fixedPC3965 : Artifact.submissionArtifact.instructionPC 3962 = 5233 := by
  calc
    Artifact.submissionArtifact.instructionPC 3962 =
        Artifact.submissionArtifact.instructionPC 3961 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3961 _ (by rfl)
    _ = 5233 := by rw [fixedPC3964]; rfl

@[simp] theorem fixedPC3966 : Artifact.submissionArtifact.instructionPC 3963 = 5234 := by
  calc
    Artifact.submissionArtifact.instructionPC 3963 =
        Artifact.submissionArtifact.instructionPC 3962 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3962 _ (by rfl)
    _ = 5234 := by rw [fixedPC3965]; rfl

@[simp] theorem fixedPC3967 : Artifact.submissionArtifact.instructionPC 3964 = 5236 := by
  calc
    Artifact.submissionArtifact.instructionPC 3964 =
        Artifact.submissionArtifact.instructionPC 3963 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3963 _ (by rfl)
    _ = 5236 := by rw [fixedPC3966]; rfl

@[simp] theorem fixedPC3968 : Artifact.submissionArtifact.instructionPC 3965 = 5237 := by
  calc
    Artifact.submissionArtifact.instructionPC 3965 =
        Artifact.submissionArtifact.instructionPC 3964 + (YulEvmCompiler.Instr.op (.Dup ⟨3, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3964 _ (by rfl)
    _ = 5237 := by rw [fixedPC3967]; rfl

@[simp] theorem fixedPC3969 : Artifact.submissionArtifact.instructionPC 3966 = 5238 := by
  calc
    Artifact.submissionArtifact.instructionPC 3966 =
        Artifact.submissionArtifact.instructionPC 3965 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3965 _ (by rfl)
    _ = 5238 := by rw [fixedPC3968]; rfl

@[simp] theorem fixedPC3970 : Artifact.submissionArtifact.instructionPC 3967 = 5239 := by
  calc
    Artifact.submissionArtifact.instructionPC 3967 =
        Artifact.submissionArtifact.instructionPC 3966 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3966 _ (by rfl)
    _ = 5239 := by rw [fixedPC3969]; rfl

@[simp] theorem fixedPC3971 : Artifact.submissionArtifact.instructionPC 3968 = 5241 := by
  calc
    Artifact.submissionArtifact.instructionPC 3968 =
        Artifact.submissionArtifact.instructionPC 3967 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3967 _ (by rfl)
    _ = 5241 := by rw [fixedPC3970]; rfl

@[simp] theorem fixedPC3972 : Artifact.submissionArtifact.instructionPC 3969 = 5242 := by
  calc
    Artifact.submissionArtifact.instructionPC 3969 =
        Artifact.submissionArtifact.instructionPC 3968 + (YulEvmCompiler.Instr.op .XOR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3968 _ (by rfl)
    _ = 5242 := by rw [fixedPC3971]; rfl

@[simp] theorem fixedPC3973 : Artifact.submissionArtifact.instructionPC 3970 = 5243 := by
  calc
    Artifact.submissionArtifact.instructionPC 3970 =
        Artifact.submissionArtifact.instructionPC 3969 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3969 _ (by rfl)
    _ = 5243 := by rw [fixedPC3972]; rfl

@[simp] theorem fixedPC3974 : Artifact.submissionArtifact.instructionPC 3971 = 5244 := by
  calc
    Artifact.submissionArtifact.instructionPC 3971 =
        Artifact.submissionArtifact.instructionPC 3970 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3970 _ (by rfl)
    _ = 5244 := by rw [fixedPC3973]; rfl

@[simp] theorem fixedPC3975 : Artifact.submissionArtifact.instructionPC 3972 = 5246 := by
  calc
    Artifact.submissionArtifact.instructionPC 3972 =
        Artifact.submissionArtifact.instructionPC 3971 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3971 _ (by rfl)
    _ = 5246 := by rw [fixedPC3974]; rfl

@[simp] theorem fixedPC3976 : Artifact.submissionArtifact.instructionPC 3973 = 5247 := by
  calc
    Artifact.submissionArtifact.instructionPC 3973 =
        Artifact.submissionArtifact.instructionPC 3972 + (YulEvmCompiler.Instr.op .XOR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3972 _ (by rfl)
    _ = 5247 := by rw [fixedPC3975]; rfl

@[simp] theorem fixedPC3977 : Artifact.submissionArtifact.instructionPC 3974 = 5248 := by
  calc
    Artifact.submissionArtifact.instructionPC 3974 =
        Artifact.submissionArtifact.instructionPC 3973 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3973 _ (by rfl)
    _ = 5248 := by rw [fixedPC3976]; rfl

@[simp] theorem fixedPC3978 : Artifact.submissionArtifact.instructionPC 3975 = 5251 := by
  calc
    Artifact.submissionArtifact.instructionPC 3975 =
        Artifact.submissionArtifact.instructionPC 3974 + (YulEvmCompiler.Instr.push 2 5273).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3974 _ (by rfl)
    _ = 5251 := by rw [fixedPC3977]; rfl

@[simp] theorem fixedPC3979 : Artifact.submissionArtifact.instructionPC 3976 = 5252 := by
  calc
    Artifact.submissionArtifact.instructionPC 3976 =
        Artifact.submissionArtifact.instructionPC 3975 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3975 _ (by rfl)
    _ = 5252 := by rw [fixedPC3978]; rfl

@[simp] theorem fixedPC3980 : Artifact.submissionArtifact.instructionPC 3977 = 5253 := by
  calc
    Artifact.submissionArtifact.instructionPC 3977 =
        Artifact.submissionArtifact.instructionPC 3976 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3976 _ (by rfl)
    _ = 5253 := by rw [fixedPC3979]; rfl

@[simp] theorem fixedPC3981 : Artifact.submissionArtifact.instructionPC 3978 = 5255 := by
  calc
    Artifact.submissionArtifact.instructionPC 3978 =
        Artifact.submissionArtifact.instructionPC 3977 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3977 _ (by rfl)
    _ = 5255 := by rw [fixedPC3980]; rfl

@[simp] theorem fixedPC3982 : Artifact.submissionArtifact.instructionPC 3979 = 5256 := by
  calc
    Artifact.submissionArtifact.instructionPC 3979 =
        Artifact.submissionArtifact.instructionPC 3978 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3978 _ (by rfl)
    _ = 5256 := by rw [fixedPC3981]; rfl

@[simp] theorem fixedPC3983 : Artifact.submissionArtifact.instructionPC 3980 = 5257 := by
  calc
    Artifact.submissionArtifact.instructionPC 3980 =
        Artifact.submissionArtifact.instructionPC 3979 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3979 _ (by rfl)
    _ = 5257 := by rw [fixedPC3982]; rfl

@[simp] theorem fixedPC3984 : Artifact.submissionArtifact.instructionPC 3981 = 5258 := by
  calc
    Artifact.submissionArtifact.instructionPC 3981 =
        Artifact.submissionArtifact.instructionPC 3980 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3980 _ (by rfl)
    _ = 5258 := by rw [fixedPC3983]; rfl

@[simp] theorem fixedPC3985 : Artifact.submissionArtifact.instructionPC 3982 = 5259 := by
  calc
    Artifact.submissionArtifact.instructionPC 3982 =
        Artifact.submissionArtifact.instructionPC 3981 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3981 _ (by rfl)
    _ = 5259 := by rw [fixedPC3984]; rfl

@[simp] theorem fixedPC3986 : Artifact.submissionArtifact.instructionPC 3983 = 5262 := by
  calc
    Artifact.submissionArtifact.instructionPC 3983 =
        Artifact.submissionArtifact.instructionPC 3982 + (YulEvmCompiler.Instr.push 2 1267).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3982 _ (by rfl)
    _ = 5262 := by rw [fixedPC3985]; rfl

@[simp] theorem fixedPC3987 : Artifact.submissionArtifact.instructionPC 3984 = 5263 := by
  calc
    Artifact.submissionArtifact.instructionPC 3984 =
        Artifact.submissionArtifact.instructionPC 3983 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3983 _ (by rfl)
    _ = 5263 := by rw [fixedPC3986]; rfl

@[simp] theorem fixedPC3988 : Artifact.submissionArtifact.instructionPC 3985 = 5264 := by
  calc
    Artifact.submissionArtifact.instructionPC 3985 =
        Artifact.submissionArtifact.instructionPC 3984 + (YulEvmCompiler.Instr.op (.Dup ⟨3, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3984 _ (by rfl)
    _ = 5264 := by rw [fixedPC3987]; rfl

@[simp] theorem fixedPC3989 : Artifact.submissionArtifact.instructionPC 3986 = 5266 := by
  calc
    Artifact.submissionArtifact.instructionPC 3986 =
        Artifact.submissionArtifact.instructionPC 3985 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3985 _ (by rfl)
    _ = 5266 := by rw [fixedPC3988]; rfl

@[simp] theorem fixedPC3990 : Artifact.submissionArtifact.instructionPC 3987 = 5267 := by
  calc
    Artifact.submissionArtifact.instructionPC 3987 =
        Artifact.submissionArtifact.instructionPC 3986 + (YulEvmCompiler.Instr.op (.Dup ⟨6, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3986 _ (by rfl)
    _ = 5267 := by rw [fixedPC3989]; rfl

@[simp] theorem fixedPC3991 : Artifact.submissionArtifact.instructionPC 3988 = 5268 := by
  calc
    Artifact.submissionArtifact.instructionPC 3988 =
        Artifact.submissionArtifact.instructionPC 3987 + (YulEvmCompiler.Instr.op (.Dup ⟨8, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3987 _ (by rfl)
    _ = 5268 := by rw [fixedPC3990]; rfl

@[simp] theorem fixedPC3992 : Artifact.submissionArtifact.instructionPC 3989 = 5269 := by
  calc
    Artifact.submissionArtifact.instructionPC 3989 =
        Artifact.submissionArtifact.instructionPC 3988 + (YulEvmCompiler.Instr.op (.Dup ⟨10, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3988 _ (by rfl)
    _ = 5269 := by rw [fixedPC3991]; rfl

@[simp] theorem fixedPC3993 : Artifact.submissionArtifact.instructionPC 3990 = 5272 := by
  calc
    Artifact.submissionArtifact.instructionPC 3990 =
        Artifact.submissionArtifact.instructionPC 3989 + (YulEvmCompiler.Instr.push 2 4886).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3989 _ (by rfl)
    _ = 5272 := by rw [fixedPC3992]; rfl

@[simp] theorem fixedPC3994 : Artifact.submissionArtifact.instructionPC 3991 = 5273 := by
  calc
    Artifact.submissionArtifact.instructionPC 3991 =
        Artifact.submissionArtifact.instructionPC 3990 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3990 _ (by rfl)
    _ = 5273 := by rw [fixedPC3993]; rfl

@[simp] theorem fixedJump5273 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5273 = true := by
  simpa only [Artifact.instructionPC, fixedPC3994] using Artifact.isValidJumpDest_index 3991 (by rfl)

@[simp] theorem fixedPC3995 : Artifact.submissionArtifact.instructionPC 3992 = 5274 := by
  calc
    Artifact.submissionArtifact.instructionPC 3992 =
        Artifact.submissionArtifact.instructionPC 3991 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3991 _ (by rfl)
    _ = 5274 := by rw [fixedPC3994]; rfl

@[simp] theorem fixedPC3996 : Artifact.submissionArtifact.instructionPC 3993 = 5275 := by
  calc
    Artifact.submissionArtifact.instructionPC 3993 =
        Artifact.submissionArtifact.instructionPC 3992 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3992 _ (by rfl)
    _ = 5275 := by rw [fixedPC3995]; rfl

@[simp] theorem fixedPC3997 : Artifact.submissionArtifact.instructionPC 3994 = 5276 := by
  calc
    Artifact.submissionArtifact.instructionPC 3994 =
        Artifact.submissionArtifact.instructionPC 3993 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3993 _ (by rfl)
    _ = 5276 := by rw [fixedPC3996]; rfl

@[simp] theorem fixedPC3998 : Artifact.submissionArtifact.instructionPC 3995 = 5277 := by
  calc
    Artifact.submissionArtifact.instructionPC 3995 =
        Artifact.submissionArtifact.instructionPC 3994 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3994 _ (by rfl)
    _ = 5277 := by rw [fixedPC3997]; rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3996 = 5280 := by
  calc
    Artifact.submissionArtifact.instructionPC 3996 =
        Artifact.submissionArtifact.instructionPC 3995 + (YulEvmCompiler.Instr.push 2 1314).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3995 _ (by rfl)
    _ = 5280 := by rw [fixedPC3998]; rfl

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3997 = 5281 := by
  calc
    Artifact.submissionArtifact.instructionPC 3997 =
        Artifact.submissionArtifact.instructionPC 3996 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3996 _ (by rfl)
    _ = 5281 := by rw [fixedPC3999]; rfl

@[simp] theorem fixedJump5281 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5281 = true := by
  simpa only [Artifact.instructionPC, fixedPC4000] using Artifact.isValidJumpDest_index 3997 (by rfl)

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3998 = 5282 := by
  calc
    Artifact.submissionArtifact.instructionPC 3998 =
        Artifact.submissionArtifact.instructionPC 3997 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3997 _ (by rfl)
    _ = 5282 := by rw [fixedPC4000]; rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3999 = 5285 := by
  calc
    Artifact.submissionArtifact.instructionPC 3999 =
        Artifact.submissionArtifact.instructionPC 3998 + (YulEvmCompiler.Instr.push 2 8352).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3998 _ (by rfl)
    _ = 5285 := by rw [fixedPC4001]; rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 4000 = 5286 := by
  calc
    Artifact.submissionArtifact.instructionPC 4000 =
        Artifact.submissionArtifact.instructionPC 3999 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3999 _ (by rfl)
    _ = 5286 := by rw [fixedPC4002]; rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 4001 = 5288 := by
  calc
    Artifact.submissionArtifact.instructionPC 4001 =
        Artifact.submissionArtifact.instructionPC 4000 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4000 _ (by rfl)
    _ = 5288 := by rw [fixedPC4003]; rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 4002 = 5289 := by
  calc
    Artifact.submissionArtifact.instructionPC 4002 =
        Artifact.submissionArtifact.instructionPC 4001 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4001 _ (by rfl)
    _ = 5289 := by rw [fixedPC4004]; rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 4003 = 5290 := by
  calc
    Artifact.submissionArtifact.instructionPC 4003 =
        Artifact.submissionArtifact.instructionPC 4002 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4002 _ (by rfl)
    _ = 5290 := by rw [fixedPC4005]; rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 4004 = 5291 := by
  calc
    Artifact.submissionArtifact.instructionPC 4004 =
        Artifact.submissionArtifact.instructionPC 4003 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4003 _ (by rfl)
    _ = 5291 := by rw [fixedPC4006]; rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 4005 = 5292 := by
  calc
    Artifact.submissionArtifact.instructionPC 4005 =
        Artifact.submissionArtifact.instructionPC 4004 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4004 _ (by rfl)
    _ = 5292 := by rw [fixedPC4007]; rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 4006 = 5293 := by
  calc
    Artifact.submissionArtifact.instructionPC 4006 =
        Artifact.submissionArtifact.instructionPC 4005 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4005 _ (by rfl)
    _ = 5293 := by rw [fixedPC4008]; rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 4007 = 5294 := by
  calc
    Artifact.submissionArtifact.instructionPC 4007 =
        Artifact.submissionArtifact.instructionPC 4006 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4006 _ (by rfl)
    _ = 5294 := by rw [fixedPC4009]; rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 4008 = 5297 := by
  calc
    Artifact.submissionArtifact.instructionPC 4008 =
        Artifact.submissionArtifact.instructionPC 4007 + (YulEvmCompiler.Instr.push 2 7264).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4007 _ (by rfl)
    _ = 5297 := by rw [fixedPC4010]; rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 4009 = 5298 := by
  calc
    Artifact.submissionArtifact.instructionPC 4009 =
        Artifact.submissionArtifact.instructionPC 4008 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4008 _ (by rfl)
    _ = 5298 := by rw [fixedPC4011]; rfl

@[simp] theorem fixedPC4013 : Artifact.submissionArtifact.instructionPC 4010 = 5301 := by
  calc
    Artifact.submissionArtifact.instructionPC 4010 =
        Artifact.submissionArtifact.instructionPC 4009 + (YulEvmCompiler.Instr.push 2 5134).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4009 _ (by rfl)
    _ = 5301 := by rw [fixedPC4012]; rfl

end Challenge.Modexp.Submission.Proofs.Fast
