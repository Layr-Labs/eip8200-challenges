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
  [opAt 3873 .JUMPDEST,
   pushAt 3874 2 9344,
   opAt 3875 .MLOAD,
   pushAt 3876 2 256,
   opAt 3877 .EQ,
   pushAt 3878 2 5087,
   opAt 3879 .JUMPI,
   pushAt 3880 2 9344,
   opAt 3881 .MLOAD,
   pushAt 3882 1 128,
   opAt 3883 .EQ,
   pushAt 3884 2 4814,
   opAt 3885 .JUMPI,
   pushAt 3886 2 9440,
   opAt 3887 .MLOAD,
   pushAt 3888 2 9408,
   opAt 3889 .MLOAD,
   opAt 3890 (.Dup ⟨0, by decide⟩),
   pushAt 3891 2 7168,
   opAt 3892 .ADD,
   pushAt 3893 2 8256,
   opAt 3894 .POP,
   opAt 3895 (.Swap ⟨0, by decide⟩),
   pushAt 3896 0 0,
   opAt 3897 (.Swap ⟨2, by decide⟩),
   pushAt 3898 2 2033,
   opAt 3899 .JUMP]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3873 .JUMPDEST,
   pushAt 3874 2 9344,
   opAt 3875 .MLOAD,
   pushAt 3876 2 256,
   opAt 3877 .EQ,
   pushAt 3878 2 5087,
   opAt 3879 .JUMPI,
   opAt 3900 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3873 .JUMPDEST,
   pushAt 3874 2 9344,
   opAt 3875 .MLOAD,
   pushAt 3876 2 256,
   opAt 3877 .EQ,
   pushAt 3878 2 5087,
   opAt 3879 .JUMPI,
   pushAt 3880 2 9344,
   opAt 3881 .MLOAD,
   pushAt 3882 1 128,
   opAt 3883 .EQ,
   pushAt 3884 2 4814,
   opAt 3885 .JUMPI,
   opAt 3728 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3901 2 8480,
   opAt 3902 .MLOAD,
   pushAt 3903 1 224,
   opAt 3904 .MLOAD,
   opAt 3905 (.Dup ⟨1, by decide⟩),
   opAt 3906 (.Dup ⟨1, by decide⟩),
   opAt 3907 .GT,
   opAt 3908 (.Swap ⟨1, by decide⟩),
   opAt 3909 .SUB,
   pushAt 3910 2 7392,
   opAt 3911 .MSTORE]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3912 2 8448,
   opAt 3913 .MLOAD,
   pushAt 3914 1 192,
   opAt 3915 .MLOAD,
   opAt 3916 (.Dup ⟨1, by decide⟩),
   opAt 3917 (.Dup ⟨1, by decide⟩),
   opAt 3918 .GT,
   opAt 3919 (.Swap ⟨1, by decide⟩),
   opAt 3920 .SUB,
   opAt 3921 (.Dup ⟨2, by decide⟩),
   opAt 3922 (.Dup ⟨1, by decide⟩),
   opAt 3923 .SUB,
   opAt 3924 (.Swap ⟨2, by decide⟩),
   opAt 3925 .GT,
   opAt 3926 .OR,
   opAt 3927 (.Swap ⟨0, by decide⟩),
   pushAt 3928 2 7360,
   opAt 3929 .MSTORE]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3930 2 8416,
   opAt 3931 .MLOAD,
   pushAt 3932 1 160,
   opAt 3933 .MLOAD,
   opAt 3934 (.Dup ⟨1, by decide⟩),
   opAt 3935 (.Dup ⟨1, by decide⟩),
   opAt 3936 .GT,
   opAt 3937 (.Swap ⟨1, by decide⟩),
   opAt 3938 .SUB,
   opAt 3939 (.Dup ⟨2, by decide⟩),
   opAt 3940 (.Dup ⟨1, by decide⟩),
   opAt 3941 .SUB,
   opAt 3942 (.Swap ⟨2, by decide⟩),
   opAt 3943 .GT,
   opAt 3944 .OR,
   opAt 3945 (.Swap ⟨0, by decide⟩),
   pushAt 3946 2 7328,
   opAt 3947 .MSTORE]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3948 2 8384,
   opAt 3949 .MLOAD,
   pushAt 3950 1 128,
   opAt 3951 .MLOAD,
   opAt 3952 (.Dup ⟨1, by decide⟩),
   opAt 3953 (.Dup ⟨1, by decide⟩),
   opAt 3954 .GT,
   opAt 3955 (.Swap ⟨1, by decide⟩),
   opAt 3956 .SUB,
   opAt 3957 (.Dup ⟨2, by decide⟩),
   opAt 3958 (.Dup ⟨1, by decide⟩),
   opAt 3959 .SUB,
   opAt 3960 (.Swap ⟨2, by decide⟩),
   opAt 3961 .GT,
   opAt 3962 .OR,
   opAt 3963 (.Swap ⟨0, by decide⟩),
   pushAt 3964 2 7296,
   opAt 3965 .MSTORE]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 3966 2 8352,
   opAt 3967 .MLOAD,
   pushAt 3968 1 96,
   opAt 3969 .MLOAD,
   opAt 3970 (.Dup ⟨1, by decide⟩),
   opAt 3971 (.Dup ⟨1, by decide⟩),
   opAt 3972 .GT,
   opAt 3973 (.Swap ⟨1, by decide⟩),
   opAt 3974 .SUB,
   opAt 3975 (.Dup ⟨2, by decide⟩),
   opAt 3976 (.Dup ⟨1, by decide⟩),
   opAt 3977 .SUB,
   opAt 3978 (.Swap ⟨2, by decide⟩),
   opAt 3979 .GT,
   opAt 3980 .OR,
   opAt 3981 (.Swap ⟨0, by decide⟩),
   pushAt 3982 2 7264,
   opAt 3983 .MSTORE]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3984 .JUMPDEST,
   pushAt 3985 2 8320,
   opAt 3986 .MLOAD,
   pushAt 3987 1 64,
   opAt 3988 .MLOAD,
   opAt 3989 (.Dup ⟨1, by decide⟩),
   opAt 3990 (.Dup ⟨1, by decide⟩),
   opAt 3991 .GT,
   opAt 3992 (.Swap ⟨1, by decide⟩),
   opAt 3993 .SUB,
   opAt 3994 (.Dup ⟨2, by decide⟩),
   opAt 3995 (.Dup ⟨1, by decide⟩),
   opAt 3996 .SUB,
   opAt 3997 (.Swap ⟨2, by decide⟩),
   opAt 3998 .GT,
   opAt 3999 .OR,
   opAt 4000 (.Swap ⟨0, by decide⟩),
   pushAt 4001 2 7232,
   opAt 4002 .MSTORE]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 4003 2 8288,
   opAt 4004 .MLOAD,
   pushAt 4005 1 32,
   opAt 4006 .MLOAD,
   opAt 4007 (.Dup ⟨1, by decide⟩),
   opAt 4008 (.Dup ⟨1, by decide⟩),
   opAt 4009 .GT,
   opAt 4010 (.Swap ⟨1, by decide⟩),
   opAt 4011 .SUB,
   opAt 4012 (.Dup ⟨2, by decide⟩),
   opAt 4013 (.Dup ⟨1, by decide⟩),
   opAt 4014 .SUB,
   opAt 4015 (.Swap ⟨2, by decide⟩),
   opAt 4016 .GT,
   opAt 4017 .OR,
   opAt 4018 (.Swap ⟨0, by decide⟩),
   pushAt 4019 2 7200,
   opAt 4020 .MSTORE]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 4021 2 8256,
   opAt 4022 .MLOAD,
   pushAt 4023 0 0,
   opAt 4024 .MLOAD,
   opAt 4025 (.Dup ⟨1, by decide⟩),
   opAt 4026 (.Dup ⟨1, by decide⟩),
   opAt 4027 .GT,
   opAt 4028 (.Swap ⟨1, by decide⟩),
   opAt 4029 .SUB,
   opAt 4030 (.Dup ⟨2, by decide⟩),
   opAt 4031 (.Dup ⟨1, by decide⟩),
   opAt 4032 .SUB,
   opAt 4033 (.Swap ⟨2, by decide⟩),
   opAt 4034 .GT,
   opAt 4035 .OR,
   opAt 4036 (.Swap ⟨0, by decide⟩),
   pushAt 4037 2 7168,
   opAt 4038 .MSTORE]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4039 .ISZERO,
   pushAt 4040 2 8224,
   opAt 4041 .MLOAD,
   opAt 4042 .OR,
   pushAt 4043 2 1087,
   opAt 4044 .NOT,
   pushAt 4045 2 5290,
   opAt 4046 .JUMP,
   opAt 4054 .JUMPDEST,
   opAt 4055 .MUL,
   pushAt 4056 2 8256,
   opAt 4057 .ADD,
   pushAt 4058 2 9344,
   opAt 4059 .MLOAD,
   opAt 4060 (.Swap ⟨1, by decide⟩),
   opAt 4061 .MCOPY,
   opAt 4062 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3729 2 8352,
   opAt 3730 .MLOAD,
   pushAt 3731 1 96,
   opAt 3732 .MLOAD,
   opAt 3733 (.Dup ⟨1, by decide⟩),
   opAt 3734 (.Dup ⟨1, by decide⟩),
   opAt 3735 .GT,
   opAt 3736 (.Swap ⟨1, by decide⟩),
   opAt 3737 .SUB,
   pushAt 3738 2 7264,
   opAt 3739 .MSTORE,
   pushAt 3740 2 5196,
   opAt 3741 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3984 .JUMPDEST,
   pushAt 3985 2 8320,
   opAt 3986 .MLOAD,
   pushAt 3987 1 64,
   opAt 3988 .MLOAD,
   opAt 3989 (.Dup ⟨1, by decide⟩),
   opAt 3990 (.Dup ⟨1, by decide⟩),
   opAt 3991 .GT,
   opAt 3992 (.Swap ⟨1, by decide⟩),
   opAt 3993 .SUB,
   opAt 3994 (.Dup ⟨2, by decide⟩),
   opAt 3995 (.Dup ⟨1, by decide⟩),
   opAt 3996 .SUB,
   opAt 3997 (.Swap ⟨2, by decide⟩),
   opAt 3998 .GT,
   opAt 3999 .OR,
   opAt 4000 (.Swap ⟨0, by decide⟩),
   pushAt 4001 2 7232,
   opAt 4002 .MSTORE]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 4003 2 8288,
   opAt 4004 .MLOAD,
   pushAt 4005 1 32,
   opAt 4006 .MLOAD,
   opAt 4007 (.Dup ⟨1, by decide⟩),
   opAt 4008 (.Dup ⟨1, by decide⟩),
   opAt 4009 .GT,
   opAt 4010 (.Swap ⟨1, by decide⟩),
   opAt 4011 .SUB,
   opAt 4012 (.Dup ⟨2, by decide⟩),
   opAt 4013 (.Dup ⟨1, by decide⟩),
   opAt 4014 .SUB,
   opAt 4015 (.Swap ⟨2, by decide⟩),
   opAt 4016 .GT,
   opAt 4017 .OR,
   opAt 4018 (.Swap ⟨0, by decide⟩),
   pushAt 4019 2 7200,
   opAt 4020 .MSTORE]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 4021 2 8256,
   opAt 4022 .MLOAD,
   pushAt 4023 0 0,
   opAt 4024 .MLOAD,
   opAt 4025 (.Dup ⟨1, by decide⟩),
   opAt 4026 (.Dup ⟨1, by decide⟩),
   opAt 4027 .GT,
   opAt 4028 (.Swap ⟨1, by decide⟩),
   opAt 4029 .SUB,
   opAt 4030 (.Dup ⟨2, by decide⟩),
   opAt 4031 (.Dup ⟨1, by decide⟩),
   opAt 4032 .SUB,
   opAt 4033 (.Swap ⟨2, by decide⟩),
   opAt 4034 .GT,
   opAt 4035 .OR,
   opAt 4036 (.Swap ⟨0, by decide⟩),
   pushAt 4037 2 7168,
   opAt 4038 .MSTORE]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4039 .ISZERO,
   pushAt 4040 2 8224,
   opAt 4041 .MLOAD,
   opAt 4042 .OR,
   pushAt 4043 2 1087,
   opAt 4044 .NOT,
   pushAt 4045 2 5290,
   opAt 4046 .JUMP,
   opAt 4054 .JUMPDEST,
   opAt 4055 .MUL,
   pushAt 4056 2 8256,
   opAt 4057 .ADD,
   pushAt 4058 2 9344,
   opAt 4059 .MLOAD,
   opAt 4060 (.Swap ⟨1, by decide⟩),
   opAt 4061 .MCOPY,
   opAt 4062 .JUMP]

@[simp] theorem fixedPC1618 : Artifact.submissionArtifact.instructionPC 1510 = 2029 := by rfl

@[simp] theorem fixedPC1619 : Artifact.submissionArtifact.instructionPC 1511 = 2032 := by
  calc
    Artifact.submissionArtifact.instructionPC 1511 =
        Artifact.submissionArtifact.instructionPC 1510 + (YulEvmCompiler.Instr.push 2 4792).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1510 _ (by rfl)
    _ = 2032 := by rw [fixedPC1618]; rfl

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3873 = 5039 := by rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5039 = true := by
  simpa only [Artifact.instructionPC, fixedPC3777] using Artifact.isValidJumpDest_index 3873 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3874 = 5040 := by
  calc
    Artifact.submissionArtifact.instructionPC 3874 =
        Artifact.submissionArtifact.instructionPC 3873 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3873 _ (by rfl)
    _ = 5040 := by rw [fixedPC3777]; rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3875 = 5043 := by
  calc
    Artifact.submissionArtifact.instructionPC 3875 =
        Artifact.submissionArtifact.instructionPC 3874 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3874 _ (by rfl)
    _ = 5043 := by rw [fixedPC3778]; rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3876 = 5044 := by
  calc
    Artifact.submissionArtifact.instructionPC 3876 =
        Artifact.submissionArtifact.instructionPC 3875 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3875 _ (by rfl)
    _ = 5044 := by rw [fixedPC3779]; rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3877 = 5047 := by
  calc
    Artifact.submissionArtifact.instructionPC 3877 =
        Artifact.submissionArtifact.instructionPC 3876 + (YulEvmCompiler.Instr.push 2 256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3876 _ (by rfl)
    _ = 5047 := by rw [fixedPC3780]; rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3878 = 5048 := by
  calc
    Artifact.submissionArtifact.instructionPC 3878 =
        Artifact.submissionArtifact.instructionPC 3877 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3877 _ (by rfl)
    _ = 5048 := by rw [fixedPC3781]; rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3879 = 5051 := by
  calc
    Artifact.submissionArtifact.instructionPC 3879 =
        Artifact.submissionArtifact.instructionPC 3878 + (YulEvmCompiler.Instr.push 2 5087).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3878 _ (by rfl)
    _ = 5051 := by rw [fixedPC3782]; rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3880 = 5052 := by
  calc
    Artifact.submissionArtifact.instructionPC 3880 =
        Artifact.submissionArtifact.instructionPC 3879 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3879 _ (by rfl)
    _ = 5052 := by rw [fixedPC3783]; rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3881 = 5055 := by
  calc
    Artifact.submissionArtifact.instructionPC 3881 =
        Artifact.submissionArtifact.instructionPC 3880 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3880 _ (by rfl)
    _ = 5055 := by rw [fixedPC3784]; rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3882 = 5056 := by
  calc
    Artifact.submissionArtifact.instructionPC 3882 =
        Artifact.submissionArtifact.instructionPC 3881 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3881 _ (by rfl)
    _ = 5056 := by rw [fixedPC3785]; rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3883 = 5058 := by
  calc
    Artifact.submissionArtifact.instructionPC 3883 =
        Artifact.submissionArtifact.instructionPC 3882 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3882 _ (by rfl)
    _ = 5058 := by rw [fixedPC3786]; rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3884 = 5059 := by
  calc
    Artifact.submissionArtifact.instructionPC 3884 =
        Artifact.submissionArtifact.instructionPC 3883 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3883 _ (by rfl)
    _ = 5059 := by rw [fixedPC3787]; rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3885 = 5062 := by
  calc
    Artifact.submissionArtifact.instructionPC 3885 =
        Artifact.submissionArtifact.instructionPC 3884 + (YulEvmCompiler.Instr.push 2 4814).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3884 _ (by rfl)
    _ = 5062 := by rw [fixedPC3788]; rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3886 = 5063 := by
  calc
    Artifact.submissionArtifact.instructionPC 3886 =
        Artifact.submissionArtifact.instructionPC 3885 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3885 _ (by rfl)
    _ = 5063 := by rw [fixedPC3789]; rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3887 = 5066 := by
  calc
    Artifact.submissionArtifact.instructionPC 3887 =
        Artifact.submissionArtifact.instructionPC 3886 + (YulEvmCompiler.Instr.push 2 9440).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3886 _ (by rfl)
    _ = 5066 := by rw [fixedPC3790]; rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3888 = 5067 := by
  calc
    Artifact.submissionArtifact.instructionPC 3888 =
        Artifact.submissionArtifact.instructionPC 3887 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3887 _ (by rfl)
    _ = 5067 := by rw [fixedPC3791]; rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3889 = 5070 := by
  calc
    Artifact.submissionArtifact.instructionPC 3889 =
        Artifact.submissionArtifact.instructionPC 3888 + (YulEvmCompiler.Instr.push 2 9408).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3888 _ (by rfl)
    _ = 5070 := by rw [fixedPC3792]; rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3890 = 5071 := by
  calc
    Artifact.submissionArtifact.instructionPC 3890 =
        Artifact.submissionArtifact.instructionPC 3889 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3889 _ (by rfl)
    _ = 5071 := by rw [fixedPC3793]; rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3891 = 5072 := by
  calc
    Artifact.submissionArtifact.instructionPC 3891 =
        Artifact.submissionArtifact.instructionPC 3890 + (YulEvmCompiler.Instr.op (.Dup ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3890 _ (by rfl)
    _ = 5072 := by rw [fixedPC3794]; rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3892 = 5075 := by
  calc
    Artifact.submissionArtifact.instructionPC 3892 =
        Artifact.submissionArtifact.instructionPC 3891 + (YulEvmCompiler.Instr.push 2 7168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3891 _ (by rfl)
    _ = 5075 := by rw [fixedPC3795]; rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3893 = 5076 := by
  calc
    Artifact.submissionArtifact.instructionPC 3893 =
        Artifact.submissionArtifact.instructionPC 3892 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3892 _ (by rfl)
    _ = 5076 := by rw [fixedPC3796]; rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3894 = 5079 := by
  calc
    Artifact.submissionArtifact.instructionPC 3894 =
        Artifact.submissionArtifact.instructionPC 3893 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3893 _ (by rfl)
    _ = 5079 := by rw [fixedPC3797]; rfl

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3895 = 5080 := by
  calc
    Artifact.submissionArtifact.instructionPC 3895 =
        Artifact.submissionArtifact.instructionPC 3894 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3894 _ (by rfl)
    _ = 5080 := by rw [fixedPC3798]; rfl

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3896 = 5081 := by
  calc
    Artifact.submissionArtifact.instructionPC 3896 =
        Artifact.submissionArtifact.instructionPC 3895 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3895 _ (by rfl)
    _ = 5081 := by rw [fixedPC3799]; rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3897 = 5082 := by
  calc
    Artifact.submissionArtifact.instructionPC 3897 =
        Artifact.submissionArtifact.instructionPC 3896 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3896 _ (by rfl)
    _ = 5082 := by rw [fixedPC3800]; rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3898 = 5083 := by
  calc
    Artifact.submissionArtifact.instructionPC 3898 =
        Artifact.submissionArtifact.instructionPC 3897 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3897 _ (by rfl)
    _ = 5083 := by rw [fixedPC3801]; rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3899 = 5086 := by
  calc
    Artifact.submissionArtifact.instructionPC 3899 =
        Artifact.submissionArtifact.instructionPC 3898 + (YulEvmCompiler.Instr.push 2 2033).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3898 _ (by rfl)
    _ = 5086 := by rw [fixedPC3802]; rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3900 = 5087 := by
  calc
    Artifact.submissionArtifact.instructionPC 3900 =
        Artifact.submissionArtifact.instructionPC 3899 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3899 _ (by rfl)
    _ = 5087 := by rw [fixedPC3803]; rfl

@[simp] theorem fixedJump5023 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5087 = true := by
  simpa only [Artifact.instructionPC, fixedPC3804] using Artifact.isValidJumpDest_index 3900 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3901 = 5088 := by
  calc
    Artifact.submissionArtifact.instructionPC 3901 =
        Artifact.submissionArtifact.instructionPC 3900 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3900 _ (by rfl)
    _ = 5088 := by rw [fixedPC3804]; rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3902 = 5091 := by
  calc
    Artifact.submissionArtifact.instructionPC 3902 =
        Artifact.submissionArtifact.instructionPC 3901 + (YulEvmCompiler.Instr.push 2 8480).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3901 _ (by rfl)
    _ = 5091 := by rw [fixedPC3805]; rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3903 = 5092 := by
  calc
    Artifact.submissionArtifact.instructionPC 3903 =
        Artifact.submissionArtifact.instructionPC 3902 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3902 _ (by rfl)
    _ = 5092 := by rw [fixedPC3806]; rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3904 = 5094 := by
  calc
    Artifact.submissionArtifact.instructionPC 3904 =
        Artifact.submissionArtifact.instructionPC 3903 + (YulEvmCompiler.Instr.push 1 224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3903 _ (by rfl)
    _ = 5094 := by rw [fixedPC3807]; rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3905 = 5095 := by
  calc
    Artifact.submissionArtifact.instructionPC 3905 =
        Artifact.submissionArtifact.instructionPC 3904 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3904 _ (by rfl)
    _ = 5095 := by rw [fixedPC3808]; rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3906 = 5096 := by
  calc
    Artifact.submissionArtifact.instructionPC 3906 =
        Artifact.submissionArtifact.instructionPC 3905 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3905 _ (by rfl)
    _ = 5096 := by rw [fixedPC3809]; rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3907 = 5097 := by
  calc
    Artifact.submissionArtifact.instructionPC 3907 =
        Artifact.submissionArtifact.instructionPC 3906 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3906 _ (by rfl)
    _ = 5097 := by rw [fixedPC3810]; rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3908 = 5098 := by
  calc
    Artifact.submissionArtifact.instructionPC 3908 =
        Artifact.submissionArtifact.instructionPC 3907 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3907 _ (by rfl)
    _ = 5098 := by rw [fixedPC3811]; rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3909 = 5099 := by
  calc
    Artifact.submissionArtifact.instructionPC 3909 =
        Artifact.submissionArtifact.instructionPC 3908 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3908 _ (by rfl)
    _ = 5099 := by rw [fixedPC3812]; rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3910 = 5100 := by
  calc
    Artifact.submissionArtifact.instructionPC 3910 =
        Artifact.submissionArtifact.instructionPC 3909 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3909 _ (by rfl)
    _ = 5100 := by rw [fixedPC3813]; rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3911 = 5103 := by
  calc
    Artifact.submissionArtifact.instructionPC 3911 =
        Artifact.submissionArtifact.instructionPC 3910 + (YulEvmCompiler.Instr.push 2 7392).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3910 _ (by rfl)
    _ = 5103 := by rw [fixedPC3814]; rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3912 = 5104 := by
  calc
    Artifact.submissionArtifact.instructionPC 3912 =
        Artifact.submissionArtifact.instructionPC 3911 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3911 _ (by rfl)
    _ = 5104 := by rw [fixedPC3815]; rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3913 = 5107 := by
  calc
    Artifact.submissionArtifact.instructionPC 3913 =
        Artifact.submissionArtifact.instructionPC 3912 + (YulEvmCompiler.Instr.push 2 8448).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3912 _ (by rfl)
    _ = 5107 := by rw [fixedPC3816]; rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3914 = 5108 := by
  calc
    Artifact.submissionArtifact.instructionPC 3914 =
        Artifact.submissionArtifact.instructionPC 3913 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3913 _ (by rfl)
    _ = 5108 := by rw [fixedPC3817]; rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3915 = 5110 := by
  calc
    Artifact.submissionArtifact.instructionPC 3915 =
        Artifact.submissionArtifact.instructionPC 3914 + (YulEvmCompiler.Instr.push 1 192).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3914 _ (by rfl)
    _ = 5110 := by rw [fixedPC3818]; rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3916 = 5111 := by
  calc
    Artifact.submissionArtifact.instructionPC 3916 =
        Artifact.submissionArtifact.instructionPC 3915 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3915 _ (by rfl)
    _ = 5111 := by rw [fixedPC3819]; rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3917 = 5112 := by
  calc
    Artifact.submissionArtifact.instructionPC 3917 =
        Artifact.submissionArtifact.instructionPC 3916 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3916 _ (by rfl)
    _ = 5112 := by rw [fixedPC3820]; rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3918 = 5113 := by
  calc
    Artifact.submissionArtifact.instructionPC 3918 =
        Artifact.submissionArtifact.instructionPC 3917 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3917 _ (by rfl)
    _ = 5113 := by rw [fixedPC3821]; rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3919 = 5114 := by
  calc
    Artifact.submissionArtifact.instructionPC 3919 =
        Artifact.submissionArtifact.instructionPC 3918 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3918 _ (by rfl)
    _ = 5114 := by rw [fixedPC3822]; rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3920 = 5115 := by
  calc
    Artifact.submissionArtifact.instructionPC 3920 =
        Artifact.submissionArtifact.instructionPC 3919 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3919 _ (by rfl)
    _ = 5115 := by rw [fixedPC3823]; rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3921 = 5116 := by
  calc
    Artifact.submissionArtifact.instructionPC 3921 =
        Artifact.submissionArtifact.instructionPC 3920 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3920 _ (by rfl)
    _ = 5116 := by rw [fixedPC3824]; rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3922 = 5117 := by
  calc
    Artifact.submissionArtifact.instructionPC 3922 =
        Artifact.submissionArtifact.instructionPC 3921 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3921 _ (by rfl)
    _ = 5117 := by rw [fixedPC3825]; rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3923 = 5118 := by
  calc
    Artifact.submissionArtifact.instructionPC 3923 =
        Artifact.submissionArtifact.instructionPC 3922 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3922 _ (by rfl)
    _ = 5118 := by rw [fixedPC3826]; rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3924 = 5119 := by
  calc
    Artifact.submissionArtifact.instructionPC 3924 =
        Artifact.submissionArtifact.instructionPC 3923 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3923 _ (by rfl)
    _ = 5119 := by rw [fixedPC3827]; rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3925 = 5120 := by
  calc
    Artifact.submissionArtifact.instructionPC 3925 =
        Artifact.submissionArtifact.instructionPC 3924 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3924 _ (by rfl)
    _ = 5120 := by rw [fixedPC3828]; rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3926 = 5121 := by
  calc
    Artifact.submissionArtifact.instructionPC 3926 =
        Artifact.submissionArtifact.instructionPC 3925 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3925 _ (by rfl)
    _ = 5121 := by rw [fixedPC3829]; rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3927 = 5122 := by
  calc
    Artifact.submissionArtifact.instructionPC 3927 =
        Artifact.submissionArtifact.instructionPC 3926 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3926 _ (by rfl)
    _ = 5122 := by rw [fixedPC3830]; rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3928 = 5123 := by
  calc
    Artifact.submissionArtifact.instructionPC 3928 =
        Artifact.submissionArtifact.instructionPC 3927 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3927 _ (by rfl)
    _ = 5123 := by rw [fixedPC3831]; rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3929 = 5126 := by
  calc
    Artifact.submissionArtifact.instructionPC 3929 =
        Artifact.submissionArtifact.instructionPC 3928 + (YulEvmCompiler.Instr.push 2 7360).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3928 _ (by rfl)
    _ = 5126 := by rw [fixedPC3832]; rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3930 = 5127 := by
  calc
    Artifact.submissionArtifact.instructionPC 3930 =
        Artifact.submissionArtifact.instructionPC 3929 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3929 _ (by rfl)
    _ = 5127 := by rw [fixedPC3833]; rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3931 = 5130 := by
  calc
    Artifact.submissionArtifact.instructionPC 3931 =
        Artifact.submissionArtifact.instructionPC 3930 + (YulEvmCompiler.Instr.push 2 8416).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3930 _ (by rfl)
    _ = 5130 := by rw [fixedPC3834]; rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3932 = 5131 := by
  calc
    Artifact.submissionArtifact.instructionPC 3932 =
        Artifact.submissionArtifact.instructionPC 3931 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3931 _ (by rfl)
    _ = 5131 := by rw [fixedPC3835]; rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3933 = 5133 := by
  calc
    Artifact.submissionArtifact.instructionPC 3933 =
        Artifact.submissionArtifact.instructionPC 3932 + (YulEvmCompiler.Instr.push 1 160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3932 _ (by rfl)
    _ = 5133 := by rw [fixedPC3836]; rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3934 = 5134 := by
  calc
    Artifact.submissionArtifact.instructionPC 3934 =
        Artifact.submissionArtifact.instructionPC 3933 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3933 _ (by rfl)
    _ = 5134 := by rw [fixedPC3837]; rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3935 = 5135 := by
  calc
    Artifact.submissionArtifact.instructionPC 3935 =
        Artifact.submissionArtifact.instructionPC 3934 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3934 _ (by rfl)
    _ = 5135 := by rw [fixedPC3838]; rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3936 = 5136 := by
  calc
    Artifact.submissionArtifact.instructionPC 3936 =
        Artifact.submissionArtifact.instructionPC 3935 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3935 _ (by rfl)
    _ = 5136 := by rw [fixedPC3839]; rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3937 = 5137 := by
  calc
    Artifact.submissionArtifact.instructionPC 3937 =
        Artifact.submissionArtifact.instructionPC 3936 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3936 _ (by rfl)
    _ = 5137 := by rw [fixedPC3840]; rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3938 = 5138 := by
  calc
    Artifact.submissionArtifact.instructionPC 3938 =
        Artifact.submissionArtifact.instructionPC 3937 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3937 _ (by rfl)
    _ = 5138 := by rw [fixedPC3841]; rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3939 = 5139 := by
  calc
    Artifact.submissionArtifact.instructionPC 3939 =
        Artifact.submissionArtifact.instructionPC 3938 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3938 _ (by rfl)
    _ = 5139 := by rw [fixedPC3842]; rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3940 = 5140 := by
  calc
    Artifact.submissionArtifact.instructionPC 3940 =
        Artifact.submissionArtifact.instructionPC 3939 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3939 _ (by rfl)
    _ = 5140 := by rw [fixedPC3843]; rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3941 = 5141 := by
  calc
    Artifact.submissionArtifact.instructionPC 3941 =
        Artifact.submissionArtifact.instructionPC 3940 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3940 _ (by rfl)
    _ = 5141 := by rw [fixedPC3844]; rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3942 = 5142 := by
  calc
    Artifact.submissionArtifact.instructionPC 3942 =
        Artifact.submissionArtifact.instructionPC 3941 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3941 _ (by rfl)
    _ = 5142 := by rw [fixedPC3845]; rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3943 = 5143 := by
  calc
    Artifact.submissionArtifact.instructionPC 3943 =
        Artifact.submissionArtifact.instructionPC 3942 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3942 _ (by rfl)
    _ = 5143 := by rw [fixedPC3846]; rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3944 = 5144 := by
  calc
    Artifact.submissionArtifact.instructionPC 3944 =
        Artifact.submissionArtifact.instructionPC 3943 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3943 _ (by rfl)
    _ = 5144 := by rw [fixedPC3847]; rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3945 = 5145 := by
  calc
    Artifact.submissionArtifact.instructionPC 3945 =
        Artifact.submissionArtifact.instructionPC 3944 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3944 _ (by rfl)
    _ = 5145 := by rw [fixedPC3848]; rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3946 = 5146 := by
  calc
    Artifact.submissionArtifact.instructionPC 3946 =
        Artifact.submissionArtifact.instructionPC 3945 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3945 _ (by rfl)
    _ = 5146 := by rw [fixedPC3849]; rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3947 = 5149 := by
  calc
    Artifact.submissionArtifact.instructionPC 3947 =
        Artifact.submissionArtifact.instructionPC 3946 + (YulEvmCompiler.Instr.push 2 7328).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3946 _ (by rfl)
    _ = 5149 := by rw [fixedPC3850]; rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3948 = 5150 := by
  calc
    Artifact.submissionArtifact.instructionPC 3948 =
        Artifact.submissionArtifact.instructionPC 3947 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3947 _ (by rfl)
    _ = 5150 := by rw [fixedPC3851]; rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3949 = 5153 := by
  calc
    Artifact.submissionArtifact.instructionPC 3949 =
        Artifact.submissionArtifact.instructionPC 3948 + (YulEvmCompiler.Instr.push 2 8384).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3948 _ (by rfl)
    _ = 5153 := by rw [fixedPC3852]; rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3950 = 5154 := by
  calc
    Artifact.submissionArtifact.instructionPC 3950 =
        Artifact.submissionArtifact.instructionPC 3949 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3949 _ (by rfl)
    _ = 5154 := by rw [fixedPC3853]; rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3951 = 5156 := by
  calc
    Artifact.submissionArtifact.instructionPC 3951 =
        Artifact.submissionArtifact.instructionPC 3950 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3950 _ (by rfl)
    _ = 5156 := by rw [fixedPC3854]; rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3952 = 5157 := by
  calc
    Artifact.submissionArtifact.instructionPC 3952 =
        Artifact.submissionArtifact.instructionPC 3951 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3951 _ (by rfl)
    _ = 5157 := by rw [fixedPC3855]; rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3953 = 5158 := by
  calc
    Artifact.submissionArtifact.instructionPC 3953 =
        Artifact.submissionArtifact.instructionPC 3952 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3952 _ (by rfl)
    _ = 5158 := by rw [fixedPC3856]; rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3954 = 5159 := by
  calc
    Artifact.submissionArtifact.instructionPC 3954 =
        Artifact.submissionArtifact.instructionPC 3953 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3953 _ (by rfl)
    _ = 5159 := by rw [fixedPC3857]; rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3955 = 5160 := by
  calc
    Artifact.submissionArtifact.instructionPC 3955 =
        Artifact.submissionArtifact.instructionPC 3954 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3954 _ (by rfl)
    _ = 5160 := by rw [fixedPC3858]; rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3956 = 5161 := by
  calc
    Artifact.submissionArtifact.instructionPC 3956 =
        Artifact.submissionArtifact.instructionPC 3955 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3955 _ (by rfl)
    _ = 5161 := by rw [fixedPC3859]; rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3957 = 5162 := by
  calc
    Artifact.submissionArtifact.instructionPC 3957 =
        Artifact.submissionArtifact.instructionPC 3956 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3956 _ (by rfl)
    _ = 5162 := by rw [fixedPC3860]; rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3958 = 5163 := by
  calc
    Artifact.submissionArtifact.instructionPC 3958 =
        Artifact.submissionArtifact.instructionPC 3957 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3957 _ (by rfl)
    _ = 5163 := by rw [fixedPC3861]; rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3959 = 5164 := by
  calc
    Artifact.submissionArtifact.instructionPC 3959 =
        Artifact.submissionArtifact.instructionPC 3958 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3958 _ (by rfl)
    _ = 5164 := by rw [fixedPC3862]; rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3960 = 5165 := by
  calc
    Artifact.submissionArtifact.instructionPC 3960 =
        Artifact.submissionArtifact.instructionPC 3959 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3959 _ (by rfl)
    _ = 5165 := by rw [fixedPC3863]; rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3961 = 5166 := by
  calc
    Artifact.submissionArtifact.instructionPC 3961 =
        Artifact.submissionArtifact.instructionPC 3960 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3960 _ (by rfl)
    _ = 5166 := by rw [fixedPC3864]; rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3962 = 5167 := by
  calc
    Artifact.submissionArtifact.instructionPC 3962 =
        Artifact.submissionArtifact.instructionPC 3961 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3961 _ (by rfl)
    _ = 5167 := by rw [fixedPC3865]; rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3963 = 5168 := by
  calc
    Artifact.submissionArtifact.instructionPC 3963 =
        Artifact.submissionArtifact.instructionPC 3962 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3962 _ (by rfl)
    _ = 5168 := by rw [fixedPC3866]; rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3964 = 5169 := by
  calc
    Artifact.submissionArtifact.instructionPC 3964 =
        Artifact.submissionArtifact.instructionPC 3963 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3963 _ (by rfl)
    _ = 5169 := by rw [fixedPC3867]; rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3965 = 5172 := by
  calc
    Artifact.submissionArtifact.instructionPC 3965 =
        Artifact.submissionArtifact.instructionPC 3964 + (YulEvmCompiler.Instr.push 2 7296).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3964 _ (by rfl)
    _ = 5172 := by rw [fixedPC3868]; rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3966 = 5173 := by
  calc
    Artifact.submissionArtifact.instructionPC 3966 =
        Artifact.submissionArtifact.instructionPC 3965 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3965 _ (by rfl)
    _ = 5173 := by rw [fixedPC3869]; rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3967 = 5176 := by
  calc
    Artifact.submissionArtifact.instructionPC 3967 =
        Artifact.submissionArtifact.instructionPC 3966 + (YulEvmCompiler.Instr.push 2 8352).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3966 _ (by rfl)
    _ = 5176 := by rw [fixedPC3871]; rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3968 = 5177 := by
  calc
    Artifact.submissionArtifact.instructionPC 3968 =
        Artifact.submissionArtifact.instructionPC 3967 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3967 _ (by rfl)
    _ = 5177 := by rw [fixedPC3872]; rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3969 = 5179 := by
  calc
    Artifact.submissionArtifact.instructionPC 3969 =
        Artifact.submissionArtifact.instructionPC 3968 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3968 _ (by rfl)
    _ = 5179 := by rw [fixedPC3873]; rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3970 = 5180 := by
  calc
    Artifact.submissionArtifact.instructionPC 3970 =
        Artifact.submissionArtifact.instructionPC 3969 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3969 _ (by rfl)
    _ = 5180 := by rw [fixedPC3874]; rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3971 = 5181 := by
  calc
    Artifact.submissionArtifact.instructionPC 3971 =
        Artifact.submissionArtifact.instructionPC 3970 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3970 _ (by rfl)
    _ = 5181 := by rw [fixedPC3875]; rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3972 = 5182 := by
  calc
    Artifact.submissionArtifact.instructionPC 3972 =
        Artifact.submissionArtifact.instructionPC 3971 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3971 _ (by rfl)
    _ = 5182 := by rw [fixedPC3876]; rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3973 = 5183 := by
  calc
    Artifact.submissionArtifact.instructionPC 3973 =
        Artifact.submissionArtifact.instructionPC 3972 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3972 _ (by rfl)
    _ = 5183 := by rw [fixedPC3877]; rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3974 = 5184 := by
  calc
    Artifact.submissionArtifact.instructionPC 3974 =
        Artifact.submissionArtifact.instructionPC 3973 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3973 _ (by rfl)
    _ = 5184 := by rw [fixedPC3878]; rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3975 = 5185 := by
  calc
    Artifact.submissionArtifact.instructionPC 3975 =
        Artifact.submissionArtifact.instructionPC 3974 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3974 _ (by rfl)
    _ = 5185 := by rw [fixedPC3879]; rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3976 = 5186 := by
  calc
    Artifact.submissionArtifact.instructionPC 3976 =
        Artifact.submissionArtifact.instructionPC 3975 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3975 _ (by rfl)
    _ = 5186 := by rw [fixedPC3880]; rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3977 = 5187 := by
  calc
    Artifact.submissionArtifact.instructionPC 3977 =
        Artifact.submissionArtifact.instructionPC 3976 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3976 _ (by rfl)
    _ = 5187 := by rw [fixedPC3881]; rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3978 = 5188 := by
  calc
    Artifact.submissionArtifact.instructionPC 3978 =
        Artifact.submissionArtifact.instructionPC 3977 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3977 _ (by rfl)
    _ = 5188 := by rw [fixedPC3882]; rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3979 = 5189 := by
  calc
    Artifact.submissionArtifact.instructionPC 3979 =
        Artifact.submissionArtifact.instructionPC 3978 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3978 _ (by rfl)
    _ = 5189 := by rw [fixedPC3883]; rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3980 = 5190 := by
  calc
    Artifact.submissionArtifact.instructionPC 3980 =
        Artifact.submissionArtifact.instructionPC 3979 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3979 _ (by rfl)
    _ = 5190 := by rw [fixedPC3884]; rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3981 = 5191 := by
  calc
    Artifact.submissionArtifact.instructionPC 3981 =
        Artifact.submissionArtifact.instructionPC 3980 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3980 _ (by rfl)
    _ = 5191 := by rw [fixedPC3885]; rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3982 = 5192 := by
  calc
    Artifact.submissionArtifact.instructionPC 3982 =
        Artifact.submissionArtifact.instructionPC 3981 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3981 _ (by rfl)
    _ = 5192 := by rw [fixedPC3886]; rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3983 = 5195 := by
  calc
    Artifact.submissionArtifact.instructionPC 3983 =
        Artifact.submissionArtifact.instructionPC 3982 + (YulEvmCompiler.Instr.push 2 7264).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3982 _ (by rfl)
    _ = 5195 := by rw [fixedPC3887]; rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3984 = 5196 := by
  calc
    Artifact.submissionArtifact.instructionPC 3984 =
        Artifact.submissionArtifact.instructionPC 3983 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3983 _ (by rfl)
    _ = 5196 := by rw [fixedPC3888]; rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5196 = true := by
  simpa only [Artifact.instructionPC, fixedPC3889] using Artifact.isValidJumpDest_index 3984 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3985 = 5197 := by
  calc
    Artifact.submissionArtifact.instructionPC 3985 =
        Artifact.submissionArtifact.instructionPC 3984 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3984 _ (by rfl)
    _ = 5197 := by rw [fixedPC3889]; rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3986 = 5200 := by
  calc
    Artifact.submissionArtifact.instructionPC 3986 =
        Artifact.submissionArtifact.instructionPC 3985 + (YulEvmCompiler.Instr.push 2 8320).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3985 _ (by rfl)
    _ = 5200 := by rw [fixedPC3890]; rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3987 = 5201 := by
  calc
    Artifact.submissionArtifact.instructionPC 3987 =
        Artifact.submissionArtifact.instructionPC 3986 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3986 _ (by rfl)
    _ = 5201 := by rw [fixedPC3891]; rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3988 = 5203 := by
  calc
    Artifact.submissionArtifact.instructionPC 3988 =
        Artifact.submissionArtifact.instructionPC 3987 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3987 _ (by rfl)
    _ = 5203 := by rw [fixedPC3892]; rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3989 = 5204 := by
  calc
    Artifact.submissionArtifact.instructionPC 3989 =
        Artifact.submissionArtifact.instructionPC 3988 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3988 _ (by rfl)
    _ = 5204 := by rw [fixedPC3893]; rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3990 = 5205 := by
  calc
    Artifact.submissionArtifact.instructionPC 3990 =
        Artifact.submissionArtifact.instructionPC 3989 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3989 _ (by rfl)
    _ = 5205 := by rw [fixedPC3894]; rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3991 = 5206 := by
  calc
    Artifact.submissionArtifact.instructionPC 3991 =
        Artifact.submissionArtifact.instructionPC 3990 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3990 _ (by rfl)
    _ = 5206 := by rw [fixedPC3895]; rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3992 = 5207 := by
  calc
    Artifact.submissionArtifact.instructionPC 3992 =
        Artifact.submissionArtifact.instructionPC 3991 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3991 _ (by rfl)
    _ = 5207 := by rw [fixedPC3896]; rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3993 = 5208 := by
  calc
    Artifact.submissionArtifact.instructionPC 3993 =
        Artifact.submissionArtifact.instructionPC 3992 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3992 _ (by rfl)
    _ = 5208 := by rw [fixedPC3897]; rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3994 = 5209 := by
  calc
    Artifact.submissionArtifact.instructionPC 3994 =
        Artifact.submissionArtifact.instructionPC 3993 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3993 _ (by rfl)
    _ = 5209 := by rw [fixedPC3898]; rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3995 = 5210 := by
  calc
    Artifact.submissionArtifact.instructionPC 3995 =
        Artifact.submissionArtifact.instructionPC 3994 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3994 _ (by rfl)
    _ = 5210 := by rw [fixedPC3899]; rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3996 = 5211 := by
  calc
    Artifact.submissionArtifact.instructionPC 3996 =
        Artifact.submissionArtifact.instructionPC 3995 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3995 _ (by rfl)
    _ = 5211 := by rw [fixedPC3900]; rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3997 = 5212 := by
  calc
    Artifact.submissionArtifact.instructionPC 3997 =
        Artifact.submissionArtifact.instructionPC 3996 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3996 _ (by rfl)
    _ = 5212 := by rw [fixedPC3901]; rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3998 = 5213 := by
  calc
    Artifact.submissionArtifact.instructionPC 3998 =
        Artifact.submissionArtifact.instructionPC 3997 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3997 _ (by rfl)
    _ = 5213 := by rw [fixedPC3902]; rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3999 = 5214 := by
  calc
    Artifact.submissionArtifact.instructionPC 3999 =
        Artifact.submissionArtifact.instructionPC 3998 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3998 _ (by rfl)
    _ = 5214 := by rw [fixedPC3903]; rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 4000 = 5215 := by
  calc
    Artifact.submissionArtifact.instructionPC 4000 =
        Artifact.submissionArtifact.instructionPC 3999 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3999 _ (by rfl)
    _ = 5215 := by rw [fixedPC3904]; rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 4001 = 5216 := by
  calc
    Artifact.submissionArtifact.instructionPC 4001 =
        Artifact.submissionArtifact.instructionPC 4000 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4000 _ (by rfl)
    _ = 5216 := by rw [fixedPC3905]; rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 4002 = 5219 := by
  calc
    Artifact.submissionArtifact.instructionPC 4002 =
        Artifact.submissionArtifact.instructionPC 4001 + (YulEvmCompiler.Instr.push 2 7232).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4001 _ (by rfl)
    _ = 5219 := by rw [fixedPC3906]; rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 4003 = 5220 := by
  calc
    Artifact.submissionArtifact.instructionPC 4003 =
        Artifact.submissionArtifact.instructionPC 4002 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4002 _ (by rfl)
    _ = 5220 := by rw [fixedPC3907]; rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 4004 = 5223 := by
  calc
    Artifact.submissionArtifact.instructionPC 4004 =
        Artifact.submissionArtifact.instructionPC 4003 + (YulEvmCompiler.Instr.push 2 8288).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4003 _ (by rfl)
    _ = 5223 := by rw [fixedPC3908]; rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 4005 = 5224 := by
  calc
    Artifact.submissionArtifact.instructionPC 4005 =
        Artifact.submissionArtifact.instructionPC 4004 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4004 _ (by rfl)
    _ = 5224 := by rw [fixedPC3909]; rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 4006 = 5226 := by
  calc
    Artifact.submissionArtifact.instructionPC 4006 =
        Artifact.submissionArtifact.instructionPC 4005 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4005 _ (by rfl)
    _ = 5226 := by rw [fixedPC3910]; rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 4007 = 5227 := by
  calc
    Artifact.submissionArtifact.instructionPC 4007 =
        Artifact.submissionArtifact.instructionPC 4006 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4006 _ (by rfl)
    _ = 5227 := by rw [fixedPC3911]; rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 4008 = 5228 := by
  calc
    Artifact.submissionArtifact.instructionPC 4008 =
        Artifact.submissionArtifact.instructionPC 4007 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4007 _ (by rfl)
    _ = 5228 := by rw [fixedPC3912]; rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 4009 = 5229 := by
  calc
    Artifact.submissionArtifact.instructionPC 4009 =
        Artifact.submissionArtifact.instructionPC 4008 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4008 _ (by rfl)
    _ = 5229 := by rw [fixedPC3913]; rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 4010 = 5230 := by
  calc
    Artifact.submissionArtifact.instructionPC 4010 =
        Artifact.submissionArtifact.instructionPC 4009 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4009 _ (by rfl)
    _ = 5230 := by rw [fixedPC3914]; rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 4011 = 5231 := by
  calc
    Artifact.submissionArtifact.instructionPC 4011 =
        Artifact.submissionArtifact.instructionPC 4010 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4010 _ (by rfl)
    _ = 5231 := by rw [fixedPC3915]; rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 4012 = 5232 := by
  calc
    Artifact.submissionArtifact.instructionPC 4012 =
        Artifact.submissionArtifact.instructionPC 4011 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4011 _ (by rfl)
    _ = 5232 := by rw [fixedPC3916]; rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 4013 = 5233 := by
  calc
    Artifact.submissionArtifact.instructionPC 4013 =
        Artifact.submissionArtifact.instructionPC 4012 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4012 _ (by rfl)
    _ = 5233 := by rw [fixedPC3917]; rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 4014 = 5234 := by
  calc
    Artifact.submissionArtifact.instructionPC 4014 =
        Artifact.submissionArtifact.instructionPC 4013 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4013 _ (by rfl)
    _ = 5234 := by rw [fixedPC3918]; rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 4015 = 5235 := by
  calc
    Artifact.submissionArtifact.instructionPC 4015 =
        Artifact.submissionArtifact.instructionPC 4014 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4014 _ (by rfl)
    _ = 5235 := by rw [fixedPC3919]; rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 4016 = 5236 := by
  calc
    Artifact.submissionArtifact.instructionPC 4016 =
        Artifact.submissionArtifact.instructionPC 4015 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4015 _ (by rfl)
    _ = 5236 := by rw [fixedPC3920]; rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 4017 = 5237 := by
  calc
    Artifact.submissionArtifact.instructionPC 4017 =
        Artifact.submissionArtifact.instructionPC 4016 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4016 _ (by rfl)
    _ = 5237 := by rw [fixedPC3921]; rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 4018 = 5238 := by
  calc
    Artifact.submissionArtifact.instructionPC 4018 =
        Artifact.submissionArtifact.instructionPC 4017 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4017 _ (by rfl)
    _ = 5238 := by rw [fixedPC3922]; rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 4019 = 5239 := by
  calc
    Artifact.submissionArtifact.instructionPC 4019 =
        Artifact.submissionArtifact.instructionPC 4018 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4018 _ (by rfl)
    _ = 5239 := by rw [fixedPC3923]; rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 4020 = 5242 := by
  calc
    Artifact.submissionArtifact.instructionPC 4020 =
        Artifact.submissionArtifact.instructionPC 4019 + (YulEvmCompiler.Instr.push 2 7200).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4019 _ (by rfl)
    _ = 5242 := by rw [fixedPC3924]; rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 4021 = 5243 := by
  calc
    Artifact.submissionArtifact.instructionPC 4021 =
        Artifact.submissionArtifact.instructionPC 4020 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4020 _ (by rfl)
    _ = 5243 := by rw [fixedPC3925]; rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 4022 = 5246 := by
  calc
    Artifact.submissionArtifact.instructionPC 4022 =
        Artifact.submissionArtifact.instructionPC 4021 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4021 _ (by rfl)
    _ = 5246 := by rw [fixedPC3926]; rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 4023 = 5247 := by
  calc
    Artifact.submissionArtifact.instructionPC 4023 =
        Artifact.submissionArtifact.instructionPC 4022 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4022 _ (by rfl)
    _ = 5247 := by rw [fixedPC3927]; rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 4024 = 5248 := by
  calc
    Artifact.submissionArtifact.instructionPC 4024 =
        Artifact.submissionArtifact.instructionPC 4023 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4023 _ (by rfl)
    _ = 5248 := by rw [fixedPC3928]; rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 4025 = 5249 := by
  calc
    Artifact.submissionArtifact.instructionPC 4025 =
        Artifact.submissionArtifact.instructionPC 4024 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4024 _ (by rfl)
    _ = 5249 := by rw [fixedPC3929]; rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 4026 = 5250 := by
  calc
    Artifact.submissionArtifact.instructionPC 4026 =
        Artifact.submissionArtifact.instructionPC 4025 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4025 _ (by rfl)
    _ = 5250 := by rw [fixedPC3930]; rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 4027 = 5251 := by
  calc
    Artifact.submissionArtifact.instructionPC 4027 =
        Artifact.submissionArtifact.instructionPC 4026 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4026 _ (by rfl)
    _ = 5251 := by rw [fixedPC3931]; rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 4028 = 5252 := by
  calc
    Artifact.submissionArtifact.instructionPC 4028 =
        Artifact.submissionArtifact.instructionPC 4027 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4027 _ (by rfl)
    _ = 5252 := by rw [fixedPC3932]; rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 4029 = 5253 := by
  calc
    Artifact.submissionArtifact.instructionPC 4029 =
        Artifact.submissionArtifact.instructionPC 4028 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4028 _ (by rfl)
    _ = 5253 := by rw [fixedPC3933]; rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 4030 = 5254 := by
  calc
    Artifact.submissionArtifact.instructionPC 4030 =
        Artifact.submissionArtifact.instructionPC 4029 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4029 _ (by rfl)
    _ = 5254 := by rw [fixedPC3934]; rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 4031 = 5255 := by
  calc
    Artifact.submissionArtifact.instructionPC 4031 =
        Artifact.submissionArtifact.instructionPC 4030 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4030 _ (by rfl)
    _ = 5255 := by rw [fixedPC3935]; rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 4032 = 5256 := by
  calc
    Artifact.submissionArtifact.instructionPC 4032 =
        Artifact.submissionArtifact.instructionPC 4031 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4031 _ (by rfl)
    _ = 5256 := by rw [fixedPC3936]; rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 4033 = 5257 := by
  calc
    Artifact.submissionArtifact.instructionPC 4033 =
        Artifact.submissionArtifact.instructionPC 4032 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4032 _ (by rfl)
    _ = 5257 := by rw [fixedPC3937]; rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 4034 = 5258 := by
  calc
    Artifact.submissionArtifact.instructionPC 4034 =
        Artifact.submissionArtifact.instructionPC 4033 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4033 _ (by rfl)
    _ = 5258 := by rw [fixedPC3938]; rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 4035 = 5259 := by
  calc
    Artifact.submissionArtifact.instructionPC 4035 =
        Artifact.submissionArtifact.instructionPC 4034 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4034 _ (by rfl)
    _ = 5259 := by rw [fixedPC3939]; rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 4036 = 5260 := by
  calc
    Artifact.submissionArtifact.instructionPC 4036 =
        Artifact.submissionArtifact.instructionPC 4035 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4035 _ (by rfl)
    _ = 5260 := by rw [fixedPC3940]; rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 4037 = 5261 := by
  calc
    Artifact.submissionArtifact.instructionPC 4037 =
        Artifact.submissionArtifact.instructionPC 4036 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4036 _ (by rfl)
    _ = 5261 := by rw [fixedPC3941]; rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 4038 = 5264 := by
  calc
    Artifact.submissionArtifact.instructionPC 4038 =
        Artifact.submissionArtifact.instructionPC 4037 + (YulEvmCompiler.Instr.push 2 7168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4037 _ (by rfl)
    _ = 5264 := by rw [fixedPC3942]; rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 4039 = 5265 := by
  calc
    Artifact.submissionArtifact.instructionPC 4039 =
        Artifact.submissionArtifact.instructionPC 4038 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4038 _ (by rfl)
    _ = 5265 := by rw [fixedPC3943]; rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 4040 = 5266 := by
  calc
    Artifact.submissionArtifact.instructionPC 4040 =
        Artifact.submissionArtifact.instructionPC 4039 + (YulEvmCompiler.Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4039 _ (by rfl)
    _ = 5266 := by rw [fixedPC3944]; rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 4041 = 5269 := by
  calc
    Artifact.submissionArtifact.instructionPC 4041 =
        Artifact.submissionArtifact.instructionPC 4040 + (YulEvmCompiler.Instr.push 2 8224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4040 _ (by rfl)
    _ = 5269 := by rw [fixedPC3945]; rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 4042 = 5270 := by
  calc
    Artifact.submissionArtifact.instructionPC 4042 =
        Artifact.submissionArtifact.instructionPC 4041 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4041 _ (by rfl)
    _ = 5270 := by rw [fixedPC3946]; rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 4043 = 5271 := by
  calc
    Artifact.submissionArtifact.instructionPC 4043 =
        Artifact.submissionArtifact.instructionPC 4042 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4042 _ (by rfl)
    _ = 5271 := by rw [fixedPC3947]; rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 4055 = 5291 := by
  decide

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 4055 = 5291 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 4056 = 5292 := by
  calc
    Artifact.submissionArtifact.instructionPC 4056 =
        Artifact.submissionArtifact.instructionPC 4055 + (YulEvmCompiler.Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4055 _ (by rfl)
    _ = 5292 := by rw [fixedPC3950]; rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 4057 = 5295 := by
  calc
    Artifact.submissionArtifact.instructionPC 4057 =
        Artifact.submissionArtifact.instructionPC 4056 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4056 _ (by rfl)
    _ = 5295 := by rw [fixedPC3951]; rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 4058 = 5296 := by
  calc
    Artifact.submissionArtifact.instructionPC 4058 =
        Artifact.submissionArtifact.instructionPC 4057 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4057 _ (by rfl)
    _ = 5296 := by rw [fixedPC3952]; rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 4059 = 5299 := by
  calc
    Artifact.submissionArtifact.instructionPC 4059 =
        Artifact.submissionArtifact.instructionPC 4058 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4058 _ (by rfl)
    _ = 5299 := by rw [fixedPC3953]; rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 4060 = 5300 := by
  calc
    Artifact.submissionArtifact.instructionPC 4060 =
        Artifact.submissionArtifact.instructionPC 4059 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4059 _ (by rfl)
    _ = 5300 := by rw [fixedPC3954]; rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 4061 = 5301 := by
  calc
    Artifact.submissionArtifact.instructionPC 4061 =
        Artifact.submissionArtifact.instructionPC 4060 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4060 _ (by rfl)
    _ = 5301 := by rw [fixedPC3955]; rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 4062 = 5302 := by
  calc
    Artifact.submissionArtifact.instructionPC 4062 =
        Artifact.submissionArtifact.instructionPC 4061 + (YulEvmCompiler.Instr.op .MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4061 _ (by rfl)
    _ = 5302 := by rw [fixedPC3956]; rfl

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

@[simp] theorem fixedPC3977 : Artifact.submissionArtifact.instructionPC 18 = 25 := by
  calc
    Artifact.submissionArtifact.instructionPC 18 =
        Artifact.submissionArtifact.instructionPC 17 + (YulEvmCompiler.Instr.push 2 47).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 17 _ (by rfl)
    _ = 25 := by rw [fixedPC3976]; rfl

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

@[simp] theorem fixedPC3992 : Artifact.submissionArtifact.instructionPC 33 = 46 := by
  calc
    Artifact.submissionArtifact.instructionPC 33 =
        Artifact.submissionArtifact.instructionPC 32 + (YulEvmCompiler.Instr.push 2 4955).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 32 _ (by rfl)
    _ = 46 := by rw [fixedPC3991]; rfl

@[simp] theorem fixedPC3993 : Artifact.submissionArtifact.instructionPC 34 = 47 := by
  calc
    Artifact.submissionArtifact.instructionPC 34 =
        Artifact.submissionArtifact.instructionPC 33 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 33 _ (by rfl)
    _ = 47 := by rw [fixedPC3992]; rfl

@[simp] theorem fixedJump5272 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 47 = true := by
  simpa only [Artifact.instructionPC, fixedPC3993] using Artifact.isValidJumpDest_index 34 (by rfl)

@[simp] theorem fixedPC3994 : Artifact.submissionArtifact.instructionPC 35 = 48 := by
  calc
    Artifact.submissionArtifact.instructionPC 35 =
        Artifact.submissionArtifact.instructionPC 34 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 34 _ (by rfl)
    _ = 48 := by rw [fixedPC3993]; rfl

@[simp] theorem fixedPC3995 : Artifact.submissionArtifact.instructionPC 36 = 49 := by
  calc
    Artifact.submissionArtifact.instructionPC 36 =
        Artifact.submissionArtifact.instructionPC 35 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 35 _ (by rfl)
    _ = 49 := by rw [fixedPC3994]; rfl

@[simp] theorem fixedPC3996 : Artifact.submissionArtifact.instructionPC 37 = 50 := by
  calc
    Artifact.submissionArtifact.instructionPC 37 =
        Artifact.submissionArtifact.instructionPC 36 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 36 _ (by rfl)
    _ = 50 := by rw [fixedPC3995]; rfl

@[simp] theorem fixedPC3997 : Artifact.submissionArtifact.instructionPC 38 = 51 := by
  calc
    Artifact.submissionArtifact.instructionPC 38 =
        Artifact.submissionArtifact.instructionPC 37 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 37 _ (by rfl)
    _ = 51 := by rw [fixedPC3996]; rfl

@[simp] theorem fixedPC3998 : Artifact.submissionArtifact.instructionPC 39 = 54 := by
  calc
    Artifact.submissionArtifact.instructionPC 39 =
        Artifact.submissionArtifact.instructionPC 38 + (YulEvmCompiler.Instr.push 2 1169).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 38 _ (by rfl)
    _ = 54 := by rw [fixedPC3997]; rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3728 = 4814 := by
  decide

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4814 = true := by
  simpa only [Artifact.instructionPC, fixedPC3999] using Artifact.isValidJumpDest_index 3728 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3729 = 4815 := by
  calc
    Artifact.submissionArtifact.instructionPC 3729 =
        Artifact.submissionArtifact.instructionPC 3728 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3728 _ (by rfl)
    _ = 4815 := by rw [fixedPC3999]; rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3730 = 4818 := by
  calc
    Artifact.submissionArtifact.instructionPC 3730 =
        Artifact.submissionArtifact.instructionPC 3729 + (YulEvmCompiler.Instr.push 2 8352).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3729 _ (by rfl)
    _ = 4818 := by rw [fixedPC4000]; rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3731 = 4819 := by
  calc
    Artifact.submissionArtifact.instructionPC 3731 =
        Artifact.submissionArtifact.instructionPC 3730 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3730 _ (by rfl)
    _ = 4819 := by rw [fixedPC4001]; rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3732 = 4821 := by
  calc
    Artifact.submissionArtifact.instructionPC 3732 =
        Artifact.submissionArtifact.instructionPC 3731 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3731 _ (by rfl)
    _ = 4821 := by rw [fixedPC4002]; rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3733 = 4822 := by
  calc
    Artifact.submissionArtifact.instructionPC 3733 =
        Artifact.submissionArtifact.instructionPC 3732 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3732 _ (by rfl)
    _ = 4822 := by rw [fixedPC4003]; rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3734 = 4823 := by
  calc
    Artifact.submissionArtifact.instructionPC 3734 =
        Artifact.submissionArtifact.instructionPC 3733 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3733 _ (by rfl)
    _ = 4823 := by rw [fixedPC4004]; rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3735 = 4824 := by
  calc
    Artifact.submissionArtifact.instructionPC 3735 =
        Artifact.submissionArtifact.instructionPC 3734 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3734 _ (by rfl)
    _ = 4824 := by rw [fixedPC4005]; rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3736 = 4825 := by
  calc
    Artifact.submissionArtifact.instructionPC 3736 =
        Artifact.submissionArtifact.instructionPC 3735 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3735 _ (by rfl)
    _ = 4825 := by rw [fixedPC4006]; rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3737 = 4826 := by
  calc
    Artifact.submissionArtifact.instructionPC 3737 =
        Artifact.submissionArtifact.instructionPC 3736 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3736 _ (by rfl)
    _ = 4826 := by rw [fixedPC4007]; rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3738 = 4827 := by
  calc
    Artifact.submissionArtifact.instructionPC 3738 =
        Artifact.submissionArtifact.instructionPC 3737 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3737 _ (by rfl)
    _ = 4827 := by rw [fixedPC4008]; rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3739 = 4830 := by
  calc
    Artifact.submissionArtifact.instructionPC 3739 =
        Artifact.submissionArtifact.instructionPC 3738 + (YulEvmCompiler.Instr.push 2 7264).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3738 _ (by rfl)
    _ = 4830 := by rw [fixedPC4009]; rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3740 = 4831 := by
  calc
    Artifact.submissionArtifact.instructionPC 3740 =
        Artifact.submissionArtifact.instructionPC 3739 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3739 _ (by rfl)
    _ = 4831 := by rw [fixedPC4010]; rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3741 = 4834 := by
  calc
    Artifact.submissionArtifact.instructionPC 3741 =
        Artifact.submissionArtifact.instructionPC 3740 + (YulEvmCompiler.Instr.push 2 5196).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3740 _ (by rfl)
    _ = 4834 := by rw [fixedPC4011]; rfl


@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2958 = 3840 := by rfl
@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3714 = 4792 := by rfl
@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3715 = 4793 := by rfl
@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3716 = 4794 := by rfl
@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3717 = 4795 := by rfl
@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3718 = 4798 := by rfl
@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3719 = 4799 := by rfl
@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3720 = 4800 := by rfl
@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3721 = 4803 := by rfl
@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3722 = 4804 := by rfl
@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3723 = 4805 := by rfl
@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3724 = 4806 := by rfl
@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3725 = 4809 := by rfl
@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3726 = 4810 := by rfl
@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3727 = 4813 := by rfl
@[simp] theorem earlyExtraPC2927 : Artifact.submissionArtifact.instructionPC 2958 = 3840 := by rfl
@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3728 = 4814 := by rfl
@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3729 = 4815 := by rfl
@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3730 = 4818 := by rfl
@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3731 = 4819 := by rfl
@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3732 = 4821 := by rfl
@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3733 = 4822 := by rfl
@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3734 = 4823 := by rfl
@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3735 = 4824 := by rfl
@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3736 = 4825 := by rfl
@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3737 = 4826 := by rfl
@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3738 = 4827 := by rfl
@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3739 = 4830 := by rfl
@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3740 = 4831 := by rfl
@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3741 = 4834 := by rfl
@[simp] theorem earlyExtraPC3918 : Artifact.submissionArtifact.instructionPC 4044 = 5274 := by rfl
@[simp] theorem earlyExtraPC3919 : Artifact.submissionArtifact.instructionPC 4045 = 5275 := by rfl
@[simp] theorem earlyExtraPC3920 : Artifact.submissionArtifact.instructionPC 4046 = 5278 := by rfl
@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 4047 = 5279 := by rfl
@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 4048 = 5280 := by rfl
@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 4049 = 5283 := by rfl
@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 4050 = 5286 := by rfl
@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 4051 = 5287 := by rfl
@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 4052 = 5288 := by rfl
@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 4053 = 5289 := by rfl
@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 4054 = 5290 := by rfl
end Challenge.Modexp.Submission.Proofs.Fast
