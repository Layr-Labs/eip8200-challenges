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
  [opAt 3833 .JUMPDEST,
   pushAt 3834 2 2688,
   opAt 3835 .MLOAD,
   pushAt 3836 2 256,
   opAt 3837 .EQ,
   pushAt 3838 2 5067,
   opAt 3839 .JUMPI,
   pushAt 3840 2 2688,
   opAt 3841 .MLOAD,
   pushAt 3842 1 128,
   opAt 3843 .EQ,
   pushAt 3844 2 4892,
   opAt 3845 .JUMPI,
   pushAt 3846 2 2784,
   opAt 3847 .MLOAD,
   pushAt 3848 2 2752,
   opAt 3849 .MLOAD,
   opAt 3850 (.Dup ⟨0, by decide⟩),
   pushAt 3851 2 1792,
   opAt 3852 .ADD,
   opAt 3853 (.Swap ⟨0, by decide⟩),
   pushAt 3854 0 0,
   opAt 3855 (.Swap ⟨2, by decide⟩),
   pushAt 3856 2 2112,
   opAt 3857 .JUMP]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3833 .JUMPDEST,
   pushAt 3834 2 2688,
   opAt 3835 .MLOAD,
   pushAt 3836 2 256,
   opAt 3837 .EQ,
   pushAt 3838 2 5067,
   opAt 3839 .JUMPI,
   opAt 3858 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3833 .JUMPDEST,
   pushAt 3834 2 2688,
   opAt 3835 .MLOAD,
   pushAt 3836 2 256,
   opAt 3837 .EQ,
   pushAt 3838 2 5067,
   opAt 3839 .JUMPI,
   pushAt 3840 2 2688,
   opAt 3841 .MLOAD,
   pushAt 3842 1 128,
   opAt 3843 .EQ,
   pushAt 3844 2 4892,
   opAt 3845 .JUMPI,
   opAt 3735 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3859 2 2336,
   opAt 3860 .MLOAD,
   pushAt 3861 1 224,
   opAt 3862 .MLOAD,
   opAt 3863 (.Dup ⟨1, by decide⟩),
   opAt 3864 (.Dup ⟨1, by decide⟩),
   opAt 3865 .GT,
   opAt 3866 (.Swap ⟨1, by decide⟩),
   opAt 3867 .SUB,
   pushAt 3868 2 2016,
   opAt 3869 .MSTORE]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3870 2 2304,
   opAt 3871 .MLOAD,
   pushAt 3872 1 192,
   opAt 3873 .MLOAD,
   opAt 3874 (.Dup ⟨1, by decide⟩),
   opAt 3875 (.Dup ⟨1, by decide⟩),
   opAt 3876 .GT,
   opAt 3877 (.Swap ⟨1, by decide⟩),
   opAt 3878 .SUB,
   opAt 3879 (.Dup ⟨2, by decide⟩),
   opAt 3880 (.Dup ⟨1, by decide⟩),
   opAt 3881 .SUB,
   opAt 3882 (.Swap ⟨2, by decide⟩),
   opAt 3883 .GT,
   opAt 3884 .OR,
   opAt 3885 (.Swap ⟨0, by decide⟩),
   pushAt 3886 2 1984,
   opAt 3887 .MSTORE]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3888 2 2272,
   opAt 3889 .MLOAD,
   pushAt 3890 1 160,
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
   pushAt 3904 2 1952,
   opAt 3905 .MSTORE]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3906 2 2240,
   opAt 3907 .MLOAD,
   pushAt 3908 1 128,
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
   pushAt 3922 2 1920,
   opAt 3923 .MSTORE]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 3924 2 2208,
   opAt 3925 .MLOAD,
   pushAt 3926 1 96,
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
   pushAt 3940 2 1888,
   opAt 3941 .MSTORE]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3942 .JUMPDEST,
   pushAt 3943 2 2176,
   opAt 3944 .MLOAD,
   pushAt 3945 1 64,
   opAt 3946 .MLOAD,
   opAt 3947 (.Dup ⟨1, by decide⟩),
   opAt 3948 (.Dup ⟨1, by decide⟩),
   opAt 3949 .GT,
   opAt 3950 (.Swap ⟨1, by decide⟩),
   opAt 3951 .SUB,
   opAt 3952 (.Dup ⟨2, by decide⟩),
   opAt 3953 (.Dup ⟨1, by decide⟩),
   opAt 3954 .SUB,
   opAt 3955 (.Swap ⟨2, by decide⟩),
   opAt 3956 .GT,
   opAt 3957 .OR,
   opAt 3958 (.Swap ⟨0, by decide⟩),
   pushAt 3959 2 1856,
   opAt 3960 .MSTORE]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3961 2 2144,
   opAt 3962 .MLOAD,
   pushAt 3963 1 32,
   opAt 3964 .MLOAD,
   opAt 3965 (.Dup ⟨1, by decide⟩),
   opAt 3966 (.Dup ⟨1, by decide⟩),
   opAt 3967 .GT,
   opAt 3968 (.Swap ⟨1, by decide⟩),
   opAt 3969 .SUB,
   opAt 3970 (.Dup ⟨2, by decide⟩),
   opAt 3971 (.Dup ⟨1, by decide⟩),
   opAt 3972 .SUB,
   opAt 3973 (.Swap ⟨2, by decide⟩),
   opAt 3974 .GT,
   opAt 3975 .OR,
   opAt 3976 (.Swap ⟨0, by decide⟩),
   pushAt 3977 2 1824,
   opAt 3978 .MSTORE]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3979 2 2112,
   opAt 3980 .MLOAD,
   pushAt 3981 0 0,
   opAt 3982 .MLOAD,
   opAt 3983 (.Dup ⟨1, by decide⟩),
   opAt 3984 (.Dup ⟨1, by decide⟩),
   opAt 3985 .GT,
   opAt 3986 (.Swap ⟨1, by decide⟩),
   opAt 3987 .SUB,
   opAt 3988 (.Dup ⟨2, by decide⟩),
   opAt 3989 (.Dup ⟨1, by decide⟩),
   opAt 3990 .SUB,
   opAt 3991 (.Swap ⟨2, by decide⟩),
   opAt 3992 .GT,
   opAt 3993 .OR,
   opAt 3994 (.Swap ⟨0, by decide⟩),
   pushAt 3995 2 1792,
   opAt 3996 .MSTORE]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3997 .ISZERO,
   pushAt 3998 2 2080,
   opAt 3999 .MLOAD,
   opAt 4000 .OR,
   pushAt 4001 2 319,
   opAt 4002 .NOT,
   pushAt 4003 2 5270,
   opAt 4004 .JUMP,
   opAt 4012 .JUMPDEST,
   opAt 4013 .MUL,
   pushAt 4014 2 2112,
   opAt 4015 .ADD,
   pushAt 4016 2 2688,
   opAt 4017 .MLOAD,
   opAt 4018 (.Swap ⟨1, by decide⟩),
   opAt 4019 .MCOPY,
   opAt 4020 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3736 2 2208,
   opAt 3737 .MLOAD,
   pushAt 3738 1 96,
   opAt 3739 .MLOAD,
   opAt 3740 (.Dup ⟨1, by decide⟩),
   opAt 3741 (.Dup ⟨1, by decide⟩),
   opAt 3742 .GT,
   opAt 3743 (.Swap ⟨1, by decide⟩),
   opAt 3744 .SUB,
   pushAt 3745 2 1888,
   opAt 3746 .MSTORE,
   pushAt 3747 2 5176,
   opAt 3748 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3942 .JUMPDEST,
   pushAt 3943 2 2176,
   opAt 3944 .MLOAD,
   pushAt 3945 1 64,
   opAt 3946 .MLOAD,
   opAt 3947 (.Dup ⟨1, by decide⟩),
   opAt 3948 (.Dup ⟨1, by decide⟩),
   opAt 3949 .GT,
   opAt 3950 (.Swap ⟨1, by decide⟩),
   opAt 3951 .SUB,
   opAt 3952 (.Dup ⟨2, by decide⟩),
   opAt 3953 (.Dup ⟨1, by decide⟩),
   opAt 3954 .SUB,
   opAt 3955 (.Swap ⟨2, by decide⟩),
   opAt 3956 .GT,
   opAt 3957 .OR,
   opAt 3958 (.Swap ⟨0, by decide⟩),
   pushAt 3959 2 1856,
   opAt 3960 .MSTORE]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3961 2 2144,
   opAt 3962 .MLOAD,
   pushAt 3963 1 32,
   opAt 3964 .MLOAD,
   opAt 3965 (.Dup ⟨1, by decide⟩),
   opAt 3966 (.Dup ⟨1, by decide⟩),
   opAt 3967 .GT,
   opAt 3968 (.Swap ⟨1, by decide⟩),
   opAt 3969 .SUB,
   opAt 3970 (.Dup ⟨2, by decide⟩),
   opAt 3971 (.Dup ⟨1, by decide⟩),
   opAt 3972 .SUB,
   opAt 3973 (.Swap ⟨2, by decide⟩),
   opAt 3974 .GT,
   opAt 3975 .OR,
   opAt 3976 (.Swap ⟨0, by decide⟩),
   pushAt 3977 2 1824,
   opAt 3978 .MSTORE]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3979 2 2112,
   opAt 3980 .MLOAD,
   pushAt 3981 0 0,
   opAt 3982 .MLOAD,
   opAt 3983 (.Dup ⟨1, by decide⟩),
   opAt 3984 (.Dup ⟨1, by decide⟩),
   opAt 3985 .GT,
   opAt 3986 (.Swap ⟨1, by decide⟩),
   opAt 3987 .SUB,
   opAt 3988 (.Dup ⟨2, by decide⟩),
   opAt 3989 (.Dup ⟨1, by decide⟩),
   opAt 3990 .SUB,
   opAt 3991 (.Swap ⟨2, by decide⟩),
   opAt 3992 .GT,
   opAt 3993 .OR,
   opAt 3994 (.Swap ⟨0, by decide⟩),
   pushAt 3995 2 1792,
   opAt 3996 .MSTORE]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3997 .ISZERO,
   pushAt 3998 2 2080,
   opAt 3999 .MLOAD,
   opAt 4000 .OR,
   pushAt 4001 2 319,
   opAt 4002 .NOT,
   pushAt 4003 2 5270,
   opAt 4004 .JUMP,
   opAt 4012 .JUMPDEST,
   opAt 4013 .MUL,
   pushAt 4014 2 2112,
   opAt 4015 .ADD,
   pushAt 4016 2 2688,
   opAt 4017 .MLOAD,
   opAt 4018 (.Swap ⟨1, by decide⟩),
   opAt 4019 .MCOPY,
   opAt 4020 .JUMP]

@[simp] theorem fixedPC1618 : Artifact.submissionArtifact.instructionPC 1547 = 2108 := by rfl

@[simp] theorem fixedPC1619 : Artifact.submissionArtifact.instructionPC 1548 = 2111 := by
  calc
    Artifact.submissionArtifact.instructionPC 1548 =
        Artifact.submissionArtifact.instructionPC 1547 + (YulEvmCompiler.Instr.push 2 4871).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1547 _ (by rfl)
    _ = 2111 := by rw [fixedPC1618]; rfl

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3833 = 5023 := by rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5023 = true := by
  simpa only [Artifact.instructionPC, fixedPC3777] using Artifact.isValidJumpDest_index 3833 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3834 = 5024 := by
  calc
    Artifact.submissionArtifact.instructionPC 3834 =
        Artifact.submissionArtifact.instructionPC 3833 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3833 _ (by rfl)
    _ = 5024 := by rw [fixedPC3777]; rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3835 = 5027 := by
  calc
    Artifact.submissionArtifact.instructionPC 3835 =
        Artifact.submissionArtifact.instructionPC 3834 + (YulEvmCompiler.Instr.push 2 2688).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3834 _ (by rfl)
    _ = 5027 := by rw [fixedPC3778]; rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3836 = 5028 := by
  calc
    Artifact.submissionArtifact.instructionPC 3836 =
        Artifact.submissionArtifact.instructionPC 3835 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3835 _ (by rfl)
    _ = 5028 := by rw [fixedPC3779]; rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3837 = 5031 := by
  calc
    Artifact.submissionArtifact.instructionPC 3837 =
        Artifact.submissionArtifact.instructionPC 3836 + (YulEvmCompiler.Instr.push 2 256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3836 _ (by rfl)
    _ = 5031 := by rw [fixedPC3780]; rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3838 = 5032 := by
  calc
    Artifact.submissionArtifact.instructionPC 3838 =
        Artifact.submissionArtifact.instructionPC 3837 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3837 _ (by rfl)
    _ = 5032 := by rw [fixedPC3781]; rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3839 = 5035 := by
  calc
    Artifact.submissionArtifact.instructionPC 3839 =
        Artifact.submissionArtifact.instructionPC 3838 + (YulEvmCompiler.Instr.push 2 5067).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3838 _ (by rfl)
    _ = 5035 := by rw [fixedPC3782]; rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3840 = 5036 := by
  calc
    Artifact.submissionArtifact.instructionPC 3840 =
        Artifact.submissionArtifact.instructionPC 3839 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3839 _ (by rfl)
    _ = 5036 := by rw [fixedPC3783]; rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3841 = 5039 := by
  calc
    Artifact.submissionArtifact.instructionPC 3841 =
        Artifact.submissionArtifact.instructionPC 3840 + (YulEvmCompiler.Instr.push 2 2688).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3840 _ (by rfl)
    _ = 5039 := by rw [fixedPC3784]; rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3842 = 5040 := by
  calc
    Artifact.submissionArtifact.instructionPC 3842 =
        Artifact.submissionArtifact.instructionPC 3841 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3841 _ (by rfl)
    _ = 5040 := by rw [fixedPC3785]; rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3843 = 5042 := by
  calc
    Artifact.submissionArtifact.instructionPC 3843 =
        Artifact.submissionArtifact.instructionPC 3842 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3842 _ (by rfl)
    _ = 5042 := by rw [fixedPC3786]; rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3844 = 5043 := by
  calc
    Artifact.submissionArtifact.instructionPC 3844 =
        Artifact.submissionArtifact.instructionPC 3843 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3843 _ (by rfl)
    _ = 5043 := by rw [fixedPC3787]; rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3845 = 5046 := by
  calc
    Artifact.submissionArtifact.instructionPC 3845 =
        Artifact.submissionArtifact.instructionPC 3844 + (YulEvmCompiler.Instr.push 2 4892).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3844 _ (by rfl)
    _ = 5046 := by rw [fixedPC3788]; rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3846 = 5047 := by
  calc
    Artifact.submissionArtifact.instructionPC 3846 =
        Artifact.submissionArtifact.instructionPC 3845 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3845 _ (by rfl)
    _ = 5047 := by rw [fixedPC3789]; rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3847 = 5050 := by
  calc
    Artifact.submissionArtifact.instructionPC 3847 =
        Artifact.submissionArtifact.instructionPC 3846 + (YulEvmCompiler.Instr.push 2 2784).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3846 _ (by rfl)
    _ = 5050 := by rw [fixedPC3790]; rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3848 = 5051 := by
  calc
    Artifact.submissionArtifact.instructionPC 3848 =
        Artifact.submissionArtifact.instructionPC 3847 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3847 _ (by rfl)
    _ = 5051 := by rw [fixedPC3791]; rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3849 = 5054 := by
  calc
    Artifact.submissionArtifact.instructionPC 3849 =
        Artifact.submissionArtifact.instructionPC 3848 + (YulEvmCompiler.Instr.push 2 2752).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3848 _ (by rfl)
    _ = 5054 := by rw [fixedPC3792]; rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3850 = 5055 := by
  calc
    Artifact.submissionArtifact.instructionPC 3850 =
        Artifact.submissionArtifact.instructionPC 3849 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3849 _ (by rfl)
    _ = 5055 := by rw [fixedPC3793]; rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3851 = 5056 := by
  calc
    Artifact.submissionArtifact.instructionPC 3851 =
        Artifact.submissionArtifact.instructionPC 3850 + (YulEvmCompiler.Instr.op (.Dup ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3850 _ (by rfl)
    _ = 5056 := by rw [fixedPC3794]; rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3852 = 5059 := by
  calc
    Artifact.submissionArtifact.instructionPC 3852 =
        Artifact.submissionArtifact.instructionPC 3851 + (YulEvmCompiler.Instr.push 2 1792).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3851 _ (by rfl)
    _ = 5059 := by rw [fixedPC3795]; rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3853 = 5060 := by
  calc
    Artifact.submissionArtifact.instructionPC 3853 =
        Artifact.submissionArtifact.instructionPC 3852 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3852 _ (by rfl)
    _ = 5060 := by rw [fixedPC3796]; rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3853 = 5060 := fixedPC3797

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3853 = 5060 := fixedPC3797

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3854 = 5061 := by
  calc
    Artifact.submissionArtifact.instructionPC 3854 =
        Artifact.submissionArtifact.instructionPC 3853 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3853 _ (by rfl)
    _ = 5061 := by rw [fixedPC3799]; rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3855 = 5062 := by
  calc
    Artifact.submissionArtifact.instructionPC 3855 =
        Artifact.submissionArtifact.instructionPC 3854 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3854 _ (by rfl)
    _ = 5062 := by rw [fixedPC3800]; rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3856 = 5063 := by
  calc
    Artifact.submissionArtifact.instructionPC 3856 =
        Artifact.submissionArtifact.instructionPC 3855 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3855 _ (by rfl)
    _ = 5063 := by rw [fixedPC3801]; rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3857 = 5066 := by
  calc
    Artifact.submissionArtifact.instructionPC 3857 =
        Artifact.submissionArtifact.instructionPC 3856 + (YulEvmCompiler.Instr.push 2 2112).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3856 _ (by rfl)
    _ = 5066 := by rw [fixedPC3802]; rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3858 = 5067 := by
  calc
    Artifact.submissionArtifact.instructionPC 3858 =
        Artifact.submissionArtifact.instructionPC 3857 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3857 _ (by rfl)
    _ = 5067 := by rw [fixedPC3803]; rfl

@[simp] theorem fixedJump5023 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5067 = true := by
  simpa only [Artifact.instructionPC, fixedPC3804] using Artifact.isValidJumpDest_index 3858 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3859 = 5068 := by
  calc
    Artifact.submissionArtifact.instructionPC 3859 =
        Artifact.submissionArtifact.instructionPC 3858 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3858 _ (by rfl)
    _ = 5068 := by rw [fixedPC3804]; rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3860 = 5071 := by
  calc
    Artifact.submissionArtifact.instructionPC 3860 =
        Artifact.submissionArtifact.instructionPC 3859 + (YulEvmCompiler.Instr.push 2 2336).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3859 _ (by rfl)
    _ = 5071 := by rw [fixedPC3805]; rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3861 = 5072 := by
  calc
    Artifact.submissionArtifact.instructionPC 3861 =
        Artifact.submissionArtifact.instructionPC 3860 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3860 _ (by rfl)
    _ = 5072 := by rw [fixedPC3806]; rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3862 = 5074 := by
  calc
    Artifact.submissionArtifact.instructionPC 3862 =
        Artifact.submissionArtifact.instructionPC 3861 + (YulEvmCompiler.Instr.push 1 224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3861 _ (by rfl)
    _ = 5074 := by rw [fixedPC3807]; rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3863 = 5075 := by
  calc
    Artifact.submissionArtifact.instructionPC 3863 =
        Artifact.submissionArtifact.instructionPC 3862 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3862 _ (by rfl)
    _ = 5075 := by rw [fixedPC3808]; rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3864 = 5076 := by
  calc
    Artifact.submissionArtifact.instructionPC 3864 =
        Artifact.submissionArtifact.instructionPC 3863 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3863 _ (by rfl)
    _ = 5076 := by rw [fixedPC3809]; rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3865 = 5077 := by
  calc
    Artifact.submissionArtifact.instructionPC 3865 =
        Artifact.submissionArtifact.instructionPC 3864 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3864 _ (by rfl)
    _ = 5077 := by rw [fixedPC3810]; rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3866 = 5078 := by
  calc
    Artifact.submissionArtifact.instructionPC 3866 =
        Artifact.submissionArtifact.instructionPC 3865 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3865 _ (by rfl)
    _ = 5078 := by rw [fixedPC3811]; rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3867 = 5079 := by
  calc
    Artifact.submissionArtifact.instructionPC 3867 =
        Artifact.submissionArtifact.instructionPC 3866 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3866 _ (by rfl)
    _ = 5079 := by rw [fixedPC3812]; rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3868 = 5080 := by
  calc
    Artifact.submissionArtifact.instructionPC 3868 =
        Artifact.submissionArtifact.instructionPC 3867 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3867 _ (by rfl)
    _ = 5080 := by rw [fixedPC3813]; rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3869 = 5083 := by
  calc
    Artifact.submissionArtifact.instructionPC 3869 =
        Artifact.submissionArtifact.instructionPC 3868 + (YulEvmCompiler.Instr.push 2 2016).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3868 _ (by rfl)
    _ = 5083 := by rw [fixedPC3814]; rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3870 = 5084 := by
  calc
    Artifact.submissionArtifact.instructionPC 3870 =
        Artifact.submissionArtifact.instructionPC 3869 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3869 _ (by rfl)
    _ = 5084 := by rw [fixedPC3815]; rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3871 = 5087 := by
  calc
    Artifact.submissionArtifact.instructionPC 3871 =
        Artifact.submissionArtifact.instructionPC 3870 + (YulEvmCompiler.Instr.push 2 2304).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3870 _ (by rfl)
    _ = 5087 := by rw [fixedPC3816]; rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3872 = 5088 := by
  calc
    Artifact.submissionArtifact.instructionPC 3872 =
        Artifact.submissionArtifact.instructionPC 3871 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3871 _ (by rfl)
    _ = 5088 := by rw [fixedPC3817]; rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3873 = 5090 := by
  calc
    Artifact.submissionArtifact.instructionPC 3873 =
        Artifact.submissionArtifact.instructionPC 3872 + (YulEvmCompiler.Instr.push 1 192).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3872 _ (by rfl)
    _ = 5090 := by rw [fixedPC3818]; rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3874 = 5091 := by
  calc
    Artifact.submissionArtifact.instructionPC 3874 =
        Artifact.submissionArtifact.instructionPC 3873 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3873 _ (by rfl)
    _ = 5091 := by rw [fixedPC3819]; rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3875 = 5092 := by
  calc
    Artifact.submissionArtifact.instructionPC 3875 =
        Artifact.submissionArtifact.instructionPC 3874 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3874 _ (by rfl)
    _ = 5092 := by rw [fixedPC3820]; rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3876 = 5093 := by
  calc
    Artifact.submissionArtifact.instructionPC 3876 =
        Artifact.submissionArtifact.instructionPC 3875 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3875 _ (by rfl)
    _ = 5093 := by rw [fixedPC3821]; rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3877 = 5094 := by
  calc
    Artifact.submissionArtifact.instructionPC 3877 =
        Artifact.submissionArtifact.instructionPC 3876 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3876 _ (by rfl)
    _ = 5094 := by rw [fixedPC3822]; rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3878 = 5095 := by
  calc
    Artifact.submissionArtifact.instructionPC 3878 =
        Artifact.submissionArtifact.instructionPC 3877 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3877 _ (by rfl)
    _ = 5095 := by rw [fixedPC3823]; rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3879 = 5096 := by
  calc
    Artifact.submissionArtifact.instructionPC 3879 =
        Artifact.submissionArtifact.instructionPC 3878 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3878 _ (by rfl)
    _ = 5096 := by rw [fixedPC3824]; rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3880 = 5097 := by
  calc
    Artifact.submissionArtifact.instructionPC 3880 =
        Artifact.submissionArtifact.instructionPC 3879 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3879 _ (by rfl)
    _ = 5097 := by rw [fixedPC3825]; rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3881 = 5098 := by
  calc
    Artifact.submissionArtifact.instructionPC 3881 =
        Artifact.submissionArtifact.instructionPC 3880 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3880 _ (by rfl)
    _ = 5098 := by rw [fixedPC3826]; rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3882 = 5099 := by
  calc
    Artifact.submissionArtifact.instructionPC 3882 =
        Artifact.submissionArtifact.instructionPC 3881 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3881 _ (by rfl)
    _ = 5099 := by rw [fixedPC3827]; rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3883 = 5100 := by
  calc
    Artifact.submissionArtifact.instructionPC 3883 =
        Artifact.submissionArtifact.instructionPC 3882 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3882 _ (by rfl)
    _ = 5100 := by rw [fixedPC3828]; rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3884 = 5101 := by
  calc
    Artifact.submissionArtifact.instructionPC 3884 =
        Artifact.submissionArtifact.instructionPC 3883 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3883 _ (by rfl)
    _ = 5101 := by rw [fixedPC3829]; rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3885 = 5102 := by
  calc
    Artifact.submissionArtifact.instructionPC 3885 =
        Artifact.submissionArtifact.instructionPC 3884 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3884 _ (by rfl)
    _ = 5102 := by rw [fixedPC3830]; rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3886 = 5103 := by
  calc
    Artifact.submissionArtifact.instructionPC 3886 =
        Artifact.submissionArtifact.instructionPC 3885 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3885 _ (by rfl)
    _ = 5103 := by rw [fixedPC3831]; rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3887 = 5106 := by
  calc
    Artifact.submissionArtifact.instructionPC 3887 =
        Artifact.submissionArtifact.instructionPC 3886 + (YulEvmCompiler.Instr.push 2 1984).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3886 _ (by rfl)
    _ = 5106 := by rw [fixedPC3832]; rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3888 = 5107 := by
  calc
    Artifact.submissionArtifact.instructionPC 3888 =
        Artifact.submissionArtifact.instructionPC 3887 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3887 _ (by rfl)
    _ = 5107 := by rw [fixedPC3833]; rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3889 = 5110 := by
  calc
    Artifact.submissionArtifact.instructionPC 3889 =
        Artifact.submissionArtifact.instructionPC 3888 + (YulEvmCompiler.Instr.push 2 2272).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3888 _ (by rfl)
    _ = 5110 := by rw [fixedPC3834]; rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3890 = 5111 := by
  calc
    Artifact.submissionArtifact.instructionPC 3890 =
        Artifact.submissionArtifact.instructionPC 3889 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3889 _ (by rfl)
    _ = 5111 := by rw [fixedPC3835]; rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3891 = 5113 := by
  calc
    Artifact.submissionArtifact.instructionPC 3891 =
        Artifact.submissionArtifact.instructionPC 3890 + (YulEvmCompiler.Instr.push 1 160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3890 _ (by rfl)
    _ = 5113 := by rw [fixedPC3836]; rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3892 = 5114 := by
  calc
    Artifact.submissionArtifact.instructionPC 3892 =
        Artifact.submissionArtifact.instructionPC 3891 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3891 _ (by rfl)
    _ = 5114 := by rw [fixedPC3837]; rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3893 = 5115 := by
  calc
    Artifact.submissionArtifact.instructionPC 3893 =
        Artifact.submissionArtifact.instructionPC 3892 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3892 _ (by rfl)
    _ = 5115 := by rw [fixedPC3838]; rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3894 = 5116 := by
  calc
    Artifact.submissionArtifact.instructionPC 3894 =
        Artifact.submissionArtifact.instructionPC 3893 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3893 _ (by rfl)
    _ = 5116 := by rw [fixedPC3839]; rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3895 = 5117 := by
  calc
    Artifact.submissionArtifact.instructionPC 3895 =
        Artifact.submissionArtifact.instructionPC 3894 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3894 _ (by rfl)
    _ = 5117 := by rw [fixedPC3840]; rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3896 = 5118 := by
  calc
    Artifact.submissionArtifact.instructionPC 3896 =
        Artifact.submissionArtifact.instructionPC 3895 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3895 _ (by rfl)
    _ = 5118 := by rw [fixedPC3841]; rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3897 = 5119 := by
  calc
    Artifact.submissionArtifact.instructionPC 3897 =
        Artifact.submissionArtifact.instructionPC 3896 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3896 _ (by rfl)
    _ = 5119 := by rw [fixedPC3842]; rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3898 = 5120 := by
  calc
    Artifact.submissionArtifact.instructionPC 3898 =
        Artifact.submissionArtifact.instructionPC 3897 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3897 _ (by rfl)
    _ = 5120 := by rw [fixedPC3843]; rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3899 = 5121 := by
  calc
    Artifact.submissionArtifact.instructionPC 3899 =
        Artifact.submissionArtifact.instructionPC 3898 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3898 _ (by rfl)
    _ = 5121 := by rw [fixedPC3844]; rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3900 = 5122 := by
  calc
    Artifact.submissionArtifact.instructionPC 3900 =
        Artifact.submissionArtifact.instructionPC 3899 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3899 _ (by rfl)
    _ = 5122 := by rw [fixedPC3845]; rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3901 = 5123 := by
  calc
    Artifact.submissionArtifact.instructionPC 3901 =
        Artifact.submissionArtifact.instructionPC 3900 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3900 _ (by rfl)
    _ = 5123 := by rw [fixedPC3846]; rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3902 = 5124 := by
  calc
    Artifact.submissionArtifact.instructionPC 3902 =
        Artifact.submissionArtifact.instructionPC 3901 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3901 _ (by rfl)
    _ = 5124 := by rw [fixedPC3847]; rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3903 = 5125 := by
  calc
    Artifact.submissionArtifact.instructionPC 3903 =
        Artifact.submissionArtifact.instructionPC 3902 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3902 _ (by rfl)
    _ = 5125 := by rw [fixedPC3848]; rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3904 = 5126 := by
  calc
    Artifact.submissionArtifact.instructionPC 3904 =
        Artifact.submissionArtifact.instructionPC 3903 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3903 _ (by rfl)
    _ = 5126 := by rw [fixedPC3849]; rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3905 = 5129 := by
  calc
    Artifact.submissionArtifact.instructionPC 3905 =
        Artifact.submissionArtifact.instructionPC 3904 + (YulEvmCompiler.Instr.push 2 1952).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3904 _ (by rfl)
    _ = 5129 := by rw [fixedPC3850]; rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3906 = 5130 := by
  calc
    Artifact.submissionArtifact.instructionPC 3906 =
        Artifact.submissionArtifact.instructionPC 3905 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3905 _ (by rfl)
    _ = 5130 := by rw [fixedPC3851]; rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3907 = 5133 := by
  calc
    Artifact.submissionArtifact.instructionPC 3907 =
        Artifact.submissionArtifact.instructionPC 3906 + (YulEvmCompiler.Instr.push 2 2240).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3906 _ (by rfl)
    _ = 5133 := by rw [fixedPC3852]; rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3908 = 5134 := by
  calc
    Artifact.submissionArtifact.instructionPC 3908 =
        Artifact.submissionArtifact.instructionPC 3907 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3907 _ (by rfl)
    _ = 5134 := by rw [fixedPC3853]; rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3909 = 5136 := by
  calc
    Artifact.submissionArtifact.instructionPC 3909 =
        Artifact.submissionArtifact.instructionPC 3908 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3908 _ (by rfl)
    _ = 5136 := by rw [fixedPC3854]; rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3910 = 5137 := by
  calc
    Artifact.submissionArtifact.instructionPC 3910 =
        Artifact.submissionArtifact.instructionPC 3909 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3909 _ (by rfl)
    _ = 5137 := by rw [fixedPC3855]; rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3911 = 5138 := by
  calc
    Artifact.submissionArtifact.instructionPC 3911 =
        Artifact.submissionArtifact.instructionPC 3910 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3910 _ (by rfl)
    _ = 5138 := by rw [fixedPC3856]; rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3912 = 5139 := by
  calc
    Artifact.submissionArtifact.instructionPC 3912 =
        Artifact.submissionArtifact.instructionPC 3911 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3911 _ (by rfl)
    _ = 5139 := by rw [fixedPC3857]; rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3913 = 5140 := by
  calc
    Artifact.submissionArtifact.instructionPC 3913 =
        Artifact.submissionArtifact.instructionPC 3912 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3912 _ (by rfl)
    _ = 5140 := by rw [fixedPC3858]; rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3914 = 5141 := by
  calc
    Artifact.submissionArtifact.instructionPC 3914 =
        Artifact.submissionArtifact.instructionPC 3913 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3913 _ (by rfl)
    _ = 5141 := by rw [fixedPC3859]; rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3915 = 5142 := by
  calc
    Artifact.submissionArtifact.instructionPC 3915 =
        Artifact.submissionArtifact.instructionPC 3914 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3914 _ (by rfl)
    _ = 5142 := by rw [fixedPC3860]; rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3916 = 5143 := by
  calc
    Artifact.submissionArtifact.instructionPC 3916 =
        Artifact.submissionArtifact.instructionPC 3915 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3915 _ (by rfl)
    _ = 5143 := by rw [fixedPC3861]; rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3917 = 5144 := by
  calc
    Artifact.submissionArtifact.instructionPC 3917 =
        Artifact.submissionArtifact.instructionPC 3916 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3916 _ (by rfl)
    _ = 5144 := by rw [fixedPC3862]; rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3918 = 5145 := by
  calc
    Artifact.submissionArtifact.instructionPC 3918 =
        Artifact.submissionArtifact.instructionPC 3917 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3917 _ (by rfl)
    _ = 5145 := by rw [fixedPC3863]; rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3919 = 5146 := by
  calc
    Artifact.submissionArtifact.instructionPC 3919 =
        Artifact.submissionArtifact.instructionPC 3918 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3918 _ (by rfl)
    _ = 5146 := by rw [fixedPC3864]; rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3920 = 5147 := by
  calc
    Artifact.submissionArtifact.instructionPC 3920 =
        Artifact.submissionArtifact.instructionPC 3919 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3919 _ (by rfl)
    _ = 5147 := by rw [fixedPC3865]; rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3921 = 5148 := by
  calc
    Artifact.submissionArtifact.instructionPC 3921 =
        Artifact.submissionArtifact.instructionPC 3920 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3920 _ (by rfl)
    _ = 5148 := by rw [fixedPC3866]; rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3922 = 5149 := by
  calc
    Artifact.submissionArtifact.instructionPC 3922 =
        Artifact.submissionArtifact.instructionPC 3921 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3921 _ (by rfl)
    _ = 5149 := by rw [fixedPC3867]; rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3923 = 5152 := by
  calc
    Artifact.submissionArtifact.instructionPC 3923 =
        Artifact.submissionArtifact.instructionPC 3922 + (YulEvmCompiler.Instr.push 2 1920).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3922 _ (by rfl)
    _ = 5152 := by rw [fixedPC3868]; rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3924 = 5153 := by
  calc
    Artifact.submissionArtifact.instructionPC 3924 =
        Artifact.submissionArtifact.instructionPC 3923 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3923 _ (by rfl)
    _ = 5153 := by rw [fixedPC3869]; rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3925 = 5156 := by
  calc
    Artifact.submissionArtifact.instructionPC 3925 =
        Artifact.submissionArtifact.instructionPC 3924 + (YulEvmCompiler.Instr.push 2 2208).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3924 _ (by rfl)
    _ = 5156 := by rw [fixedPC3871]; rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3926 = 5157 := by
  calc
    Artifact.submissionArtifact.instructionPC 3926 =
        Artifact.submissionArtifact.instructionPC 3925 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3925 _ (by rfl)
    _ = 5157 := by rw [fixedPC3872]; rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3927 = 5159 := by
  calc
    Artifact.submissionArtifact.instructionPC 3927 =
        Artifact.submissionArtifact.instructionPC 3926 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3926 _ (by rfl)
    _ = 5159 := by rw [fixedPC3873]; rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3928 = 5160 := by
  calc
    Artifact.submissionArtifact.instructionPC 3928 =
        Artifact.submissionArtifact.instructionPC 3927 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3927 _ (by rfl)
    _ = 5160 := by rw [fixedPC3874]; rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3929 = 5161 := by
  calc
    Artifact.submissionArtifact.instructionPC 3929 =
        Artifact.submissionArtifact.instructionPC 3928 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3928 _ (by rfl)
    _ = 5161 := by rw [fixedPC3875]; rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3930 = 5162 := by
  calc
    Artifact.submissionArtifact.instructionPC 3930 =
        Artifact.submissionArtifact.instructionPC 3929 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3929 _ (by rfl)
    _ = 5162 := by rw [fixedPC3876]; rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3931 = 5163 := by
  calc
    Artifact.submissionArtifact.instructionPC 3931 =
        Artifact.submissionArtifact.instructionPC 3930 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3930 _ (by rfl)
    _ = 5163 := by rw [fixedPC3877]; rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3932 = 5164 := by
  calc
    Artifact.submissionArtifact.instructionPC 3932 =
        Artifact.submissionArtifact.instructionPC 3931 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3931 _ (by rfl)
    _ = 5164 := by rw [fixedPC3878]; rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3933 = 5165 := by
  calc
    Artifact.submissionArtifact.instructionPC 3933 =
        Artifact.submissionArtifact.instructionPC 3932 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3932 _ (by rfl)
    _ = 5165 := by rw [fixedPC3879]; rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3934 = 5166 := by
  calc
    Artifact.submissionArtifact.instructionPC 3934 =
        Artifact.submissionArtifact.instructionPC 3933 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3933 _ (by rfl)
    _ = 5166 := by rw [fixedPC3880]; rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3935 = 5167 := by
  calc
    Artifact.submissionArtifact.instructionPC 3935 =
        Artifact.submissionArtifact.instructionPC 3934 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3934 _ (by rfl)
    _ = 5167 := by rw [fixedPC3881]; rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3936 = 5168 := by
  calc
    Artifact.submissionArtifact.instructionPC 3936 =
        Artifact.submissionArtifact.instructionPC 3935 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3935 _ (by rfl)
    _ = 5168 := by rw [fixedPC3882]; rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3937 = 5169 := by
  calc
    Artifact.submissionArtifact.instructionPC 3937 =
        Artifact.submissionArtifact.instructionPC 3936 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3936 _ (by rfl)
    _ = 5169 := by rw [fixedPC3883]; rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3938 = 5170 := by
  calc
    Artifact.submissionArtifact.instructionPC 3938 =
        Artifact.submissionArtifact.instructionPC 3937 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3937 _ (by rfl)
    _ = 5170 := by rw [fixedPC3884]; rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3939 = 5171 := by
  calc
    Artifact.submissionArtifact.instructionPC 3939 =
        Artifact.submissionArtifact.instructionPC 3938 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3938 _ (by rfl)
    _ = 5171 := by rw [fixedPC3885]; rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3940 = 5172 := by
  calc
    Artifact.submissionArtifact.instructionPC 3940 =
        Artifact.submissionArtifact.instructionPC 3939 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3939 _ (by rfl)
    _ = 5172 := by rw [fixedPC3886]; rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3941 = 5175 := by
  calc
    Artifact.submissionArtifact.instructionPC 3941 =
        Artifact.submissionArtifact.instructionPC 3940 + (YulEvmCompiler.Instr.push 2 1888).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3940 _ (by rfl)
    _ = 5175 := by rw [fixedPC3887]; rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3942 = 5176 := by
  calc
    Artifact.submissionArtifact.instructionPC 3942 =
        Artifact.submissionArtifact.instructionPC 3941 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3941 _ (by rfl)
    _ = 5176 := by rw [fixedPC3888]; rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5176 = true := by
  simpa only [Artifact.instructionPC, fixedPC3889] using Artifact.isValidJumpDest_index 3942 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3943 = 5177 := by
  calc
    Artifact.submissionArtifact.instructionPC 3943 =
        Artifact.submissionArtifact.instructionPC 3942 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3942 _ (by rfl)
    _ = 5177 := by rw [fixedPC3889]; rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3944 = 5180 := by
  calc
    Artifact.submissionArtifact.instructionPC 3944 =
        Artifact.submissionArtifact.instructionPC 3943 + (YulEvmCompiler.Instr.push 2 2176).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3943 _ (by rfl)
    _ = 5180 := by rw [fixedPC3890]; rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3945 = 5181 := by
  calc
    Artifact.submissionArtifact.instructionPC 3945 =
        Artifact.submissionArtifact.instructionPC 3944 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3944 _ (by rfl)
    _ = 5181 := by rw [fixedPC3891]; rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3946 = 5183 := by
  calc
    Artifact.submissionArtifact.instructionPC 3946 =
        Artifact.submissionArtifact.instructionPC 3945 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3945 _ (by rfl)
    _ = 5183 := by rw [fixedPC3892]; rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3947 = 5184 := by
  calc
    Artifact.submissionArtifact.instructionPC 3947 =
        Artifact.submissionArtifact.instructionPC 3946 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3946 _ (by rfl)
    _ = 5184 := by rw [fixedPC3893]; rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3948 = 5185 := by
  calc
    Artifact.submissionArtifact.instructionPC 3948 =
        Artifact.submissionArtifact.instructionPC 3947 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3947 _ (by rfl)
    _ = 5185 := by rw [fixedPC3894]; rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3949 = 5186 := by
  calc
    Artifact.submissionArtifact.instructionPC 3949 =
        Artifact.submissionArtifact.instructionPC 3948 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3948 _ (by rfl)
    _ = 5186 := by rw [fixedPC3895]; rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3950 = 5187 := by
  calc
    Artifact.submissionArtifact.instructionPC 3950 =
        Artifact.submissionArtifact.instructionPC 3949 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3949 _ (by rfl)
    _ = 5187 := by rw [fixedPC3896]; rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3951 = 5188 := by
  calc
    Artifact.submissionArtifact.instructionPC 3951 =
        Artifact.submissionArtifact.instructionPC 3950 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3950 _ (by rfl)
    _ = 5188 := by rw [fixedPC3897]; rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3952 = 5189 := by
  calc
    Artifact.submissionArtifact.instructionPC 3952 =
        Artifact.submissionArtifact.instructionPC 3951 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3951 _ (by rfl)
    _ = 5189 := by rw [fixedPC3898]; rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3953 = 5190 := by
  calc
    Artifact.submissionArtifact.instructionPC 3953 =
        Artifact.submissionArtifact.instructionPC 3952 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3952 _ (by rfl)
    _ = 5190 := by rw [fixedPC3899]; rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3954 = 5191 := by
  calc
    Artifact.submissionArtifact.instructionPC 3954 =
        Artifact.submissionArtifact.instructionPC 3953 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3953 _ (by rfl)
    _ = 5191 := by rw [fixedPC3900]; rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3955 = 5192 := by
  calc
    Artifact.submissionArtifact.instructionPC 3955 =
        Artifact.submissionArtifact.instructionPC 3954 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3954 _ (by rfl)
    _ = 5192 := by rw [fixedPC3901]; rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3956 = 5193 := by
  calc
    Artifact.submissionArtifact.instructionPC 3956 =
        Artifact.submissionArtifact.instructionPC 3955 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3955 _ (by rfl)
    _ = 5193 := by rw [fixedPC3902]; rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3957 = 5194 := by
  calc
    Artifact.submissionArtifact.instructionPC 3957 =
        Artifact.submissionArtifact.instructionPC 3956 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3956 _ (by rfl)
    _ = 5194 := by rw [fixedPC3903]; rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3958 = 5195 := by
  calc
    Artifact.submissionArtifact.instructionPC 3958 =
        Artifact.submissionArtifact.instructionPC 3957 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3957 _ (by rfl)
    _ = 5195 := by rw [fixedPC3904]; rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3959 = 5196 := by
  calc
    Artifact.submissionArtifact.instructionPC 3959 =
        Artifact.submissionArtifact.instructionPC 3958 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3958 _ (by rfl)
    _ = 5196 := by rw [fixedPC3905]; rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3960 = 5199 := by
  calc
    Artifact.submissionArtifact.instructionPC 3960 =
        Artifact.submissionArtifact.instructionPC 3959 + (YulEvmCompiler.Instr.push 2 1856).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3959 _ (by rfl)
    _ = 5199 := by rw [fixedPC3906]; rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3961 = 5200 := by
  calc
    Artifact.submissionArtifact.instructionPC 3961 =
        Artifact.submissionArtifact.instructionPC 3960 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3960 _ (by rfl)
    _ = 5200 := by rw [fixedPC3907]; rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3962 = 5203 := by
  calc
    Artifact.submissionArtifact.instructionPC 3962 =
        Artifact.submissionArtifact.instructionPC 3961 + (YulEvmCompiler.Instr.push 2 2144).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3961 _ (by rfl)
    _ = 5203 := by rw [fixedPC3908]; rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3963 = 5204 := by
  calc
    Artifact.submissionArtifact.instructionPC 3963 =
        Artifact.submissionArtifact.instructionPC 3962 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3962 _ (by rfl)
    _ = 5204 := by rw [fixedPC3909]; rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3964 = 5206 := by
  calc
    Artifact.submissionArtifact.instructionPC 3964 =
        Artifact.submissionArtifact.instructionPC 3963 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3963 _ (by rfl)
    _ = 5206 := by rw [fixedPC3910]; rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3965 = 5207 := by
  calc
    Artifact.submissionArtifact.instructionPC 3965 =
        Artifact.submissionArtifact.instructionPC 3964 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3964 _ (by rfl)
    _ = 5207 := by rw [fixedPC3911]; rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3966 = 5208 := by
  calc
    Artifact.submissionArtifact.instructionPC 3966 =
        Artifact.submissionArtifact.instructionPC 3965 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3965 _ (by rfl)
    _ = 5208 := by rw [fixedPC3912]; rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3967 = 5209 := by
  calc
    Artifact.submissionArtifact.instructionPC 3967 =
        Artifact.submissionArtifact.instructionPC 3966 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3966 _ (by rfl)
    _ = 5209 := by rw [fixedPC3913]; rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3968 = 5210 := by
  calc
    Artifact.submissionArtifact.instructionPC 3968 =
        Artifact.submissionArtifact.instructionPC 3967 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3967 _ (by rfl)
    _ = 5210 := by rw [fixedPC3914]; rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3969 = 5211 := by
  calc
    Artifact.submissionArtifact.instructionPC 3969 =
        Artifact.submissionArtifact.instructionPC 3968 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3968 _ (by rfl)
    _ = 5211 := by rw [fixedPC3915]; rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3970 = 5212 := by
  calc
    Artifact.submissionArtifact.instructionPC 3970 =
        Artifact.submissionArtifact.instructionPC 3969 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3969 _ (by rfl)
    _ = 5212 := by rw [fixedPC3916]; rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3971 = 5213 := by
  calc
    Artifact.submissionArtifact.instructionPC 3971 =
        Artifact.submissionArtifact.instructionPC 3970 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3970 _ (by rfl)
    _ = 5213 := by rw [fixedPC3917]; rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3972 = 5214 := by
  calc
    Artifact.submissionArtifact.instructionPC 3972 =
        Artifact.submissionArtifact.instructionPC 3971 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3971 _ (by rfl)
    _ = 5214 := by rw [fixedPC3918]; rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3973 = 5215 := by
  calc
    Artifact.submissionArtifact.instructionPC 3973 =
        Artifact.submissionArtifact.instructionPC 3972 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3972 _ (by rfl)
    _ = 5215 := by rw [fixedPC3919]; rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3974 = 5216 := by
  calc
    Artifact.submissionArtifact.instructionPC 3974 =
        Artifact.submissionArtifact.instructionPC 3973 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3973 _ (by rfl)
    _ = 5216 := by rw [fixedPC3920]; rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3975 = 5217 := by
  calc
    Artifact.submissionArtifact.instructionPC 3975 =
        Artifact.submissionArtifact.instructionPC 3974 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3974 _ (by rfl)
    _ = 5217 := by rw [fixedPC3921]; rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3976 = 5218 := by
  calc
    Artifact.submissionArtifact.instructionPC 3976 =
        Artifact.submissionArtifact.instructionPC 3975 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3975 _ (by rfl)
    _ = 5218 := by rw [fixedPC3922]; rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3977 = 5219 := by
  calc
    Artifact.submissionArtifact.instructionPC 3977 =
        Artifact.submissionArtifact.instructionPC 3976 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3976 _ (by rfl)
    _ = 5219 := by rw [fixedPC3923]; rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3978 = 5222 := by
  calc
    Artifact.submissionArtifact.instructionPC 3978 =
        Artifact.submissionArtifact.instructionPC 3977 + (YulEvmCompiler.Instr.push 2 1824).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3977 _ (by rfl)
    _ = 5222 := by rw [fixedPC3924]; rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3979 = 5223 := by
  calc
    Artifact.submissionArtifact.instructionPC 3979 =
        Artifact.submissionArtifact.instructionPC 3978 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3978 _ (by rfl)
    _ = 5223 := by rw [fixedPC3925]; rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3980 = 5226 := by
  calc
    Artifact.submissionArtifact.instructionPC 3980 =
        Artifact.submissionArtifact.instructionPC 3979 + (YulEvmCompiler.Instr.push 2 2112).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3979 _ (by rfl)
    _ = 5226 := by rw [fixedPC3926]; rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3981 = 5227 := by
  calc
    Artifact.submissionArtifact.instructionPC 3981 =
        Artifact.submissionArtifact.instructionPC 3980 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3980 _ (by rfl)
    _ = 5227 := by rw [fixedPC3927]; rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3982 = 5228 := by
  calc
    Artifact.submissionArtifact.instructionPC 3982 =
        Artifact.submissionArtifact.instructionPC 3981 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3981 _ (by rfl)
    _ = 5228 := by rw [fixedPC3928]; rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3983 = 5229 := by
  calc
    Artifact.submissionArtifact.instructionPC 3983 =
        Artifact.submissionArtifact.instructionPC 3982 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3982 _ (by rfl)
    _ = 5229 := by rw [fixedPC3929]; rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3984 = 5230 := by
  calc
    Artifact.submissionArtifact.instructionPC 3984 =
        Artifact.submissionArtifact.instructionPC 3983 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3983 _ (by rfl)
    _ = 5230 := by rw [fixedPC3930]; rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3985 = 5231 := by
  calc
    Artifact.submissionArtifact.instructionPC 3985 =
        Artifact.submissionArtifact.instructionPC 3984 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3984 _ (by rfl)
    _ = 5231 := by rw [fixedPC3931]; rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3986 = 5232 := by
  calc
    Artifact.submissionArtifact.instructionPC 3986 =
        Artifact.submissionArtifact.instructionPC 3985 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3985 _ (by rfl)
    _ = 5232 := by rw [fixedPC3932]; rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3987 = 5233 := by
  calc
    Artifact.submissionArtifact.instructionPC 3987 =
        Artifact.submissionArtifact.instructionPC 3986 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3986 _ (by rfl)
    _ = 5233 := by rw [fixedPC3933]; rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3988 = 5234 := by
  calc
    Artifact.submissionArtifact.instructionPC 3988 =
        Artifact.submissionArtifact.instructionPC 3987 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3987 _ (by rfl)
    _ = 5234 := by rw [fixedPC3934]; rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3989 = 5235 := by
  calc
    Artifact.submissionArtifact.instructionPC 3989 =
        Artifact.submissionArtifact.instructionPC 3988 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3988 _ (by rfl)
    _ = 5235 := by rw [fixedPC3935]; rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3990 = 5236 := by
  calc
    Artifact.submissionArtifact.instructionPC 3990 =
        Artifact.submissionArtifact.instructionPC 3989 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3989 _ (by rfl)
    _ = 5236 := by rw [fixedPC3936]; rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3991 = 5237 := by
  calc
    Artifact.submissionArtifact.instructionPC 3991 =
        Artifact.submissionArtifact.instructionPC 3990 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3990 _ (by rfl)
    _ = 5237 := by rw [fixedPC3937]; rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3992 = 5238 := by
  calc
    Artifact.submissionArtifact.instructionPC 3992 =
        Artifact.submissionArtifact.instructionPC 3991 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3991 _ (by rfl)
    _ = 5238 := by rw [fixedPC3938]; rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3993 = 5239 := by
  calc
    Artifact.submissionArtifact.instructionPC 3993 =
        Artifact.submissionArtifact.instructionPC 3992 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3992 _ (by rfl)
    _ = 5239 := by rw [fixedPC3939]; rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3994 = 5240 := by
  calc
    Artifact.submissionArtifact.instructionPC 3994 =
        Artifact.submissionArtifact.instructionPC 3993 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3993 _ (by rfl)
    _ = 5240 := by rw [fixedPC3940]; rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3995 = 5241 := by
  calc
    Artifact.submissionArtifact.instructionPC 3995 =
        Artifact.submissionArtifact.instructionPC 3994 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3994 _ (by rfl)
    _ = 5241 := by rw [fixedPC3941]; rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3996 = 5244 := by
  calc
    Artifact.submissionArtifact.instructionPC 3996 =
        Artifact.submissionArtifact.instructionPC 3995 + (YulEvmCompiler.Instr.push 2 1792).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3995 _ (by rfl)
    _ = 5244 := by rw [fixedPC3942]; rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3997 = 5245 := by
  calc
    Artifact.submissionArtifact.instructionPC 3997 =
        Artifact.submissionArtifact.instructionPC 3996 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3996 _ (by rfl)
    _ = 5245 := by rw [fixedPC3943]; rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3998 = 5246 := by
  calc
    Artifact.submissionArtifact.instructionPC 3998 =
        Artifact.submissionArtifact.instructionPC 3997 + (YulEvmCompiler.Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3997 _ (by rfl)
    _ = 5246 := by rw [fixedPC3944]; rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3999 = 5249 := by
  calc
    Artifact.submissionArtifact.instructionPC 3999 =
        Artifact.submissionArtifact.instructionPC 3998 + (YulEvmCompiler.Instr.push 2 2080).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3998 _ (by rfl)
    _ = 5249 := by rw [fixedPC3945]; rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 4000 = 5250 := by
  calc
    Artifact.submissionArtifact.instructionPC 4000 =
        Artifact.submissionArtifact.instructionPC 3999 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3999 _ (by rfl)
    _ = 5250 := by rw [fixedPC3946]; rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 4001 = 5251 := by
  calc
    Artifact.submissionArtifact.instructionPC 4001 =
        Artifact.submissionArtifact.instructionPC 4000 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4000 _ (by rfl)
    _ = 5251 := by rw [fixedPC3947]; rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 4013 = 5271 := by
  decide

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 4013 = 5271 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 4014 = 5272 := by
  calc
    Artifact.submissionArtifact.instructionPC 4014 =
        Artifact.submissionArtifact.instructionPC 4013 + (YulEvmCompiler.Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4013 _ (by rfl)
    _ = 5272 := by rw [fixedPC3950]; rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 4015 = 5275 := by
  calc
    Artifact.submissionArtifact.instructionPC 4015 =
        Artifact.submissionArtifact.instructionPC 4014 + (YulEvmCompiler.Instr.push 2 2112).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4014 _ (by rfl)
    _ = 5275 := by rw [fixedPC3951]; rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 4016 = 5276 := by
  calc
    Artifact.submissionArtifact.instructionPC 4016 =
        Artifact.submissionArtifact.instructionPC 4015 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4015 _ (by rfl)
    _ = 5276 := by rw [fixedPC3952]; rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 4017 = 5279 := by
  calc
    Artifact.submissionArtifact.instructionPC 4017 =
        Artifact.submissionArtifact.instructionPC 4016 + (YulEvmCompiler.Instr.push 2 2688).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4016 _ (by rfl)
    _ = 5279 := by rw [fixedPC3953]; rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 4018 = 5280 := by
  calc
    Artifact.submissionArtifact.instructionPC 4018 =
        Artifact.submissionArtifact.instructionPC 4017 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4017 _ (by rfl)
    _ = 5280 := by rw [fixedPC3954]; rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 4019 = 5281 := by
  calc
    Artifact.submissionArtifact.instructionPC 4019 =
        Artifact.submissionArtifact.instructionPC 4018 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4018 _ (by rfl)
    _ = 5281 := by rw [fixedPC3955]; rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 4020 = 5282 := by
  calc
    Artifact.submissionArtifact.instructionPC 4020 =
        Artifact.submissionArtifact.instructionPC 4019 + (YulEvmCompiler.Instr.op .MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4019 _ (by rfl)
    _ = 5282 := by rw [fixedPC3956]; rfl

@[simp] theorem fixedPC3958 : Artifact.submissionArtifact.instructionPC 0 = 0 := by rfl

@[simp] theorem fixedPC3959 : Artifact.submissionArtifact.instructionPC 0 = 0 := by rfl

@[simp] theorem fixedPC3960 : Artifact.submissionArtifact.instructionPC 1 = 1 := by
  calc
    Artifact.submissionArtifact.instructionPC 1 =
        Artifact.submissionArtifact.instructionPC 0 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 0 _ (by rfl)
    _ = 1 := by rw [fixedPC3959]; rfl

@[simp] theorem fixedPC3961 : Artifact.submissionArtifact.instructionPC 2 = 2 := by
  calc
    Artifact.submissionArtifact.instructionPC 2 =
        Artifact.submissionArtifact.instructionPC 1 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1 _ (by rfl)
    _ = 2 := by rw [fixedPC3960]; rfl

@[simp] theorem fixedPC3962 : Artifact.submissionArtifact.instructionPC 3 = 4 := by
  calc
    Artifact.submissionArtifact.instructionPC 3 =
        Artifact.submissionArtifact.instructionPC 2 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2 _ (by rfl)
    _ = 4 := by rw [fixedPC3961]; rfl

@[simp] theorem fixedPC3963 : Artifact.submissionArtifact.instructionPC 4 = 5 := by
  calc
    Artifact.submissionArtifact.instructionPC 4 =
        Artifact.submissionArtifact.instructionPC 3 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3 _ (by rfl)
    _ = 5 := by rw [fixedPC3962]; rfl

@[simp] theorem fixedPC3964 : Artifact.submissionArtifact.instructionPC 5 = 7 := by
  calc
    Artifact.submissionArtifact.instructionPC 5 =
        Artifact.submissionArtifact.instructionPC 4 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4 _ (by rfl)
    _ = 7 := by rw [fixedPC3963]; rfl

@[simp] theorem fixedPC3965 : Artifact.submissionArtifact.instructionPC 6 = 8 := by
  calc
    Artifact.submissionArtifact.instructionPC 6 =
        Artifact.submissionArtifact.instructionPC 5 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 5 _ (by rfl)
    _ = 8 := by rw [fixedPC3964]; rfl

@[simp] theorem fixedPC3966 : Artifact.submissionArtifact.instructionPC 7 = 10 := by
  calc
    Artifact.submissionArtifact.instructionPC 7 =
        Artifact.submissionArtifact.instructionPC 6 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 6 _ (by rfl)
    _ = 10 := by rw [fixedPC3965]; rfl

@[simp] theorem fixedPC3967 : Artifact.submissionArtifact.instructionPC 8 = 11 := by
  calc
    Artifact.submissionArtifact.instructionPC 8 =
        Artifact.submissionArtifact.instructionPC 7 + (YulEvmCompiler.Instr.op (.Dup ⟨3, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 7 _ (by rfl)
    _ = 11 := by rw [fixedPC3966]; rfl

@[simp] theorem fixedPC3968 : Artifact.submissionArtifact.instructionPC 9 = 12 := by
  calc
    Artifact.submissionArtifact.instructionPC 9 =
        Artifact.submissionArtifact.instructionPC 8 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 8 _ (by rfl)
    _ = 12 := by rw [fixedPC3967]; rfl

@[simp] theorem fixedPC3969 : Artifact.submissionArtifact.instructionPC 10 = 13 := by
  calc
    Artifact.submissionArtifact.instructionPC 10 =
        Artifact.submissionArtifact.instructionPC 9 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 9 _ (by rfl)
    _ = 13 := by rw [fixedPC3968]; rfl

@[simp] theorem fixedPC3970 : Artifact.submissionArtifact.instructionPC 11 = 15 := by
  calc
    Artifact.submissionArtifact.instructionPC 11 =
        Artifact.submissionArtifact.instructionPC 10 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 10 _ (by rfl)
    _ = 15 := by rw [fixedPC3969]; rfl

@[simp] theorem fixedPC3971 : Artifact.submissionArtifact.instructionPC 12 = 16 := by
  calc
    Artifact.submissionArtifact.instructionPC 12 =
        Artifact.submissionArtifact.instructionPC 11 + (YulEvmCompiler.Instr.op .XOR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 11 _ (by rfl)
    _ = 16 := by rw [fixedPC3970]; rfl

@[simp] theorem fixedPC3972 : Artifact.submissionArtifact.instructionPC 13 = 17 := by
  calc
    Artifact.submissionArtifact.instructionPC 13 =
        Artifact.submissionArtifact.instructionPC 12 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 12 _ (by rfl)
    _ = 17 := by rw [fixedPC3971]; rfl

@[simp] theorem fixedPC3973 : Artifact.submissionArtifact.instructionPC 14 = 18 := by
  calc
    Artifact.submissionArtifact.instructionPC 14 =
        Artifact.submissionArtifact.instructionPC 13 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 13 _ (by rfl)
    _ = 18 := by rw [fixedPC3972]; rfl

@[simp] theorem fixedPC3974 : Artifact.submissionArtifact.instructionPC 15 = 20 := by
  calc
    Artifact.submissionArtifact.instructionPC 15 =
        Artifact.submissionArtifact.instructionPC 14 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 14 _ (by rfl)
    _ = 20 := by rw [fixedPC3973]; rfl

@[simp] theorem fixedPC3975 : Artifact.submissionArtifact.instructionPC 16 = 21 := by
  calc
    Artifact.submissionArtifact.instructionPC 16 =
        Artifact.submissionArtifact.instructionPC 15 + (YulEvmCompiler.Instr.op .XOR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 15 _ (by rfl)
    _ = 21 := by rw [fixedPC3974]; rfl

@[simp] theorem fixedPC3976 : Artifact.submissionArtifact.instructionPC 17 = 22 := by
  calc
    Artifact.submissionArtifact.instructionPC 17 =
        Artifact.submissionArtifact.instructionPC 16 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 16 _ (by rfl)
    _ = 22 := by rw [fixedPC3975]; rfl

@[simp] theorem fixedPC3977 : Artifact.submissionArtifact.instructionPC 18 = 25 := by rfl

@[simp] theorem fixedPC3978 : Artifact.submissionArtifact.instructionPC 19 = 26 := by
  calc
    Artifact.submissionArtifact.instructionPC 19 =
        Artifact.submissionArtifact.instructionPC 18 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 18 _ (by rfl)
    _ = 26 := by rw [fixedPC3977]; rfl

@[simp] theorem fixedPC3979 : Artifact.submissionArtifact.instructionPC 20 = 27 := by
  calc
    Artifact.submissionArtifact.instructionPC 20 =
        Artifact.submissionArtifact.instructionPC 19 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 19 _ (by rfl)
    _ = 27 := by rw [fixedPC3978]; rfl

@[simp] theorem fixedPC3980 : Artifact.submissionArtifact.instructionPC 21 = 29 := by
  calc
    Artifact.submissionArtifact.instructionPC 21 =
        Artifact.submissionArtifact.instructionPC 20 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 20 _ (by rfl)
    _ = 29 := by rw [fixedPC3979]; rfl

@[simp] theorem fixedPC3981 : Artifact.submissionArtifact.instructionPC 22 = 30 := by
  calc
    Artifact.submissionArtifact.instructionPC 22 =
        Artifact.submissionArtifact.instructionPC 21 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 21 _ (by rfl)
    _ = 30 := by rw [fixedPC3980]; rfl

@[simp] theorem fixedPC3982 : Artifact.submissionArtifact.instructionPC 23 = 31 := by
  calc
    Artifact.submissionArtifact.instructionPC 23 =
        Artifact.submissionArtifact.instructionPC 22 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 22 _ (by rfl)
    _ = 31 := by rw [fixedPC3981]; rfl

@[simp] theorem fixedPC3983 : Artifact.submissionArtifact.instructionPC 24 = 32 := by
  calc
    Artifact.submissionArtifact.instructionPC 24 =
        Artifact.submissionArtifact.instructionPC 23 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 23 _ (by rfl)
    _ = 32 := by rw [fixedPC3982]; rfl

@[simp] theorem fixedPC3984 : Artifact.submissionArtifact.instructionPC 25 = 33 := by
  calc
    Artifact.submissionArtifact.instructionPC 25 =
        Artifact.submissionArtifact.instructionPC 24 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 24 _ (by rfl)
    _ = 33 := by rw [fixedPC3983]; rfl

@[simp] theorem fixedPC3985 : Artifact.submissionArtifact.instructionPC 26 = 36 := by
  calc
    Artifact.submissionArtifact.instructionPC 26 =
        Artifact.submissionArtifact.instructionPC 25 + (YulEvmCompiler.Instr.push 2 1186).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 25 _ (by rfl)
    _ = 36 := by rw [fixedPC3984]; rfl

@[simp] theorem fixedPC3986 : Artifact.submissionArtifact.instructionPC 27 = 37 := by
  calc
    Artifact.submissionArtifact.instructionPC 27 =
        Artifact.submissionArtifact.instructionPC 26 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 26 _ (by rfl)
    _ = 37 := by rw [fixedPC3985]; rfl

@[simp] theorem fixedPC3987 : Artifact.submissionArtifact.instructionPC 28 = 38 := by
  calc
    Artifact.submissionArtifact.instructionPC 28 =
        Artifact.submissionArtifact.instructionPC 27 + (YulEvmCompiler.Instr.op (.Dup ⟨3, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 27 _ (by rfl)
    _ = 38 := by rw [fixedPC3986]; rfl

@[simp] theorem fixedPC3988 : Artifact.submissionArtifact.instructionPC 29 = 40 := by
  calc
    Artifact.submissionArtifact.instructionPC 29 =
        Artifact.submissionArtifact.instructionPC 28 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 28 _ (by rfl)
    _ = 40 := by rw [fixedPC3987]; rfl

@[simp] theorem fixedPC3989 : Artifact.submissionArtifact.instructionPC 30 = 41 := by
  calc
    Artifact.submissionArtifact.instructionPC 30 =
        Artifact.submissionArtifact.instructionPC 29 + (YulEvmCompiler.Instr.op (.Dup ⟨6, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 29 _ (by rfl)
    _ = 41 := by rw [fixedPC3988]; rfl

@[simp] theorem fixedPC3990 : Artifact.submissionArtifact.instructionPC 31 = 42 := by
  calc
    Artifact.submissionArtifact.instructionPC 31 =
        Artifact.submissionArtifact.instructionPC 30 + (YulEvmCompiler.Instr.op (.Dup ⟨8, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 30 _ (by rfl)
    _ = 42 := by rw [fixedPC3989]; rfl

@[simp] theorem fixedPC3991 : Artifact.submissionArtifact.instructionPC 32 = 43 := by
  calc
    Artifact.submissionArtifact.instructionPC 32 =
        Artifact.submissionArtifact.instructionPC 31 + (YulEvmCompiler.Instr.op (.Dup ⟨10, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 31 _ (by rfl)
    _ = 43 := by rw [fixedPC3990]; rfl

@[simp] theorem fixedPC3992 : Artifact.submissionArtifact.instructionPC 32 = 43 := by rfl

@[simp] theorem fixedPC3993 : Artifact.submissionArtifact.instructionPC 71 = 127 := by rfl

@[simp] theorem fixedJump5272 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 127 = true := by
  simpa only [Artifact.instructionPC, fixedPC3993] using Artifact.isValidJumpDest_index 71 (by rfl)

@[simp] theorem fixedPC3994 : Artifact.submissionArtifact.instructionPC 72 = 128 := by
  calc
    Artifact.submissionArtifact.instructionPC 72 =
        Artifact.submissionArtifact.instructionPC 71 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 71 _ (by rfl)
    _ = 128 := by rw [fixedPC3993]; rfl

@[simp] theorem fixedPC3995 : Artifact.submissionArtifact.instructionPC 73 = 129 := by
  calc
    Artifact.submissionArtifact.instructionPC 73 =
        Artifact.submissionArtifact.instructionPC 72 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 72 _ (by rfl)
    _ = 129 := by rw [fixedPC3994]; rfl

@[simp] theorem fixedPC3996 : Artifact.submissionArtifact.instructionPC 74 = 130 := by
  calc
    Artifact.submissionArtifact.instructionPC 74 =
        Artifact.submissionArtifact.instructionPC 73 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 73 _ (by rfl)
    _ = 130 := by rw [fixedPC3995]; rfl

@[simp] theorem fixedPC3997 : Artifact.submissionArtifact.instructionPC 75 = 131 := by
  calc
    Artifact.submissionArtifact.instructionPC 75 =
        Artifact.submissionArtifact.instructionPC 74 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 74 _ (by rfl)
    _ = 131 := by rw [fixedPC3996]; rfl

@[simp] theorem fixedPC3998 : Artifact.submissionArtifact.instructionPC 76 = 134 := by
  calc
    Artifact.submissionArtifact.instructionPC 76 =
        Artifact.submissionArtifact.instructionPC 75 + (YulEvmCompiler.Instr.push 2 1251).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 75 _ (by rfl)
    _ = 134 := by rw [fixedPC3997]; rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3735 = 4892 := by
  decide

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4892 = true := by
  simpa only [Artifact.instructionPC, fixedPC3999] using Artifact.isValidJumpDest_index 3735 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3736 = 4893 := by
  calc
    Artifact.submissionArtifact.instructionPC 3736 =
        Artifact.submissionArtifact.instructionPC 3735 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3735 _ (by rfl)
    _ = 4893 := by rw [fixedPC3999]; rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3737 = 4896 := by
  calc
    Artifact.submissionArtifact.instructionPC 3737 =
        Artifact.submissionArtifact.instructionPC 3736 + (YulEvmCompiler.Instr.push 2 2208).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3736 _ (by rfl)
    _ = 4896 := by rw [fixedPC4000]; rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3738 = 4897 := by
  calc
    Artifact.submissionArtifact.instructionPC 3738 =
        Artifact.submissionArtifact.instructionPC 3737 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3737 _ (by rfl)
    _ = 4897 := by rw [fixedPC4001]; rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3739 = 4899 := by
  calc
    Artifact.submissionArtifact.instructionPC 3739 =
        Artifact.submissionArtifact.instructionPC 3738 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3738 _ (by rfl)
    _ = 4899 := by rw [fixedPC4002]; rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3740 = 4900 := by
  calc
    Artifact.submissionArtifact.instructionPC 3740 =
        Artifact.submissionArtifact.instructionPC 3739 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3739 _ (by rfl)
    _ = 4900 := by rw [fixedPC4003]; rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3741 = 4901 := by
  calc
    Artifact.submissionArtifact.instructionPC 3741 =
        Artifact.submissionArtifact.instructionPC 3740 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3740 _ (by rfl)
    _ = 4901 := by rw [fixedPC4004]; rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3742 = 4902 := by
  calc
    Artifact.submissionArtifact.instructionPC 3742 =
        Artifact.submissionArtifact.instructionPC 3741 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3741 _ (by rfl)
    _ = 4902 := by rw [fixedPC4005]; rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3743 = 4903 := by
  calc
    Artifact.submissionArtifact.instructionPC 3743 =
        Artifact.submissionArtifact.instructionPC 3742 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3742 _ (by rfl)
    _ = 4903 := by rw [fixedPC4006]; rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3744 = 4904 := by
  calc
    Artifact.submissionArtifact.instructionPC 3744 =
        Artifact.submissionArtifact.instructionPC 3743 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3743 _ (by rfl)
    _ = 4904 := by rw [fixedPC4007]; rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3745 = 4905 := by
  calc
    Artifact.submissionArtifact.instructionPC 3745 =
        Artifact.submissionArtifact.instructionPC 3744 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3744 _ (by rfl)
    _ = 4905 := by rw [fixedPC4008]; rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3746 = 4908 := by
  calc
    Artifact.submissionArtifact.instructionPC 3746 =
        Artifact.submissionArtifact.instructionPC 3745 + (YulEvmCompiler.Instr.push 2 1888).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3745 _ (by rfl)
    _ = 4908 := by rw [fixedPC4009]; rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3747 = 4909 := by
  calc
    Artifact.submissionArtifact.instructionPC 3747 =
        Artifact.submissionArtifact.instructionPC 3746 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3746 _ (by rfl)
    _ = 4909 := by rw [fixedPC4010]; rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3748 = 4912 := by
  calc
    Artifact.submissionArtifact.instructionPC 3748 =
        Artifact.submissionArtifact.instructionPC 3747 + (YulEvmCompiler.Instr.push 2 5176).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3747 _ (by rfl)
    _ = 4912 := by rw [fixedPC4011]; rfl


@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2935 = 3873 := by rfl
@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3722 = 4871 := by rfl
@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3723 = 4872 := by rfl
@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3724 = 4873 := by rfl
@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3725 = 4874 := by rfl
@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3726 = 4877 := by rfl
@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3727 = 4878 := by rfl
@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3728 = 4879 := by rfl
@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3729 = 4882 := by rfl
@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3730 = 4883 := by rfl
@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3731 = 4884 := by rfl
@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3731 = 4884 := by rfl
@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3732 = 4887 := by rfl
@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3733 = 4888 := by rfl
@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3734 = 4891 := by rfl
@[simp] theorem earlyExtraPC2927 : Artifact.submissionArtifact.instructionPC 2935 = 3873 := by rfl
@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3735 = 4892 := by rfl
@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3736 = 4893 := by rfl
@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3737 = 4896 := by rfl
@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3738 = 4897 := by rfl
@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3739 = 4899 := by rfl
@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3740 = 4900 := by rfl
@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3741 = 4901 := by rfl
@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3742 = 4902 := by rfl
@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3743 = 4903 := by rfl
@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3744 = 4904 := by rfl
@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3745 = 4905 := by rfl
@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3746 = 4908 := by rfl
@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3747 = 4909 := by rfl
@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3748 = 4912 := by rfl
@[simp] theorem earlyExtraPC3918 : Artifact.submissionArtifact.instructionPC 4002 = 5254 := by rfl
@[simp] theorem earlyExtraPC3919 : Artifact.submissionArtifact.instructionPC 4003 = 5255 := by rfl
@[simp] theorem earlyExtraPC3920 : Artifact.submissionArtifact.instructionPC 4004 = 5258 := by rfl
@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 4005 = 5259 := by rfl
@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 4006 = 5260 := by rfl
@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 4007 = 5263 := by rfl
@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 4008 = 5266 := by rfl
@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 4009 = 5267 := by rfl
@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 4010 = 5268 := by rfl
@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 4011 = 5269 := by rfl
@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 4012 = 5270 := by rfl
end Challenge.Modexp.Submission.Proofs.Fast
