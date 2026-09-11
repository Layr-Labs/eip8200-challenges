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
  [opAt 1575 .JUMPDEST,
   pushAt 1576 2 4978,
   opAt 1577 .JUMP,
   opAt 3710 .JUMPDEST,
   pushAt 3711 2 9344,
   opAt 3712 .MLOAD,
   pushAt 3713 2 256,
   opAt 3714 .EQ,
   pushAt 3715 2 5026,
   opAt 3716 .JUMPI,
   pushAt 3717 2 9344,
   opAt 3718 .MLOAD,
   pushAt 3719 1 128,
   opAt 3720 .EQ,
   pushAt 3721 2 5312,
   opAt 3722 .JUMPI,
   pushAt 3723 2 9440,
   opAt 3724 .MLOAD,
   pushAt 3725 2 9408,
   opAt 3726 .MLOAD,
   opAt 3727 (.Dup ⟨0, by decide⟩),
   pushAt 3728 2 7168,
   opAt 3729 .ADD,
   pushAt 3730 2 8256,
   opAt 3731 .POP,
   opAt 3732 (.Swap ⟨0, by decide⟩),
   pushAt 3733 0 0,
   opAt 3734 (.Swap ⟨2, by decide⟩),
   pushAt 3735 2 2144,
   opAt 3736 .JUMP]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1575 .JUMPDEST,
   pushAt 1576 2 4978,
   opAt 1577 .JUMP,
   opAt 3710 .JUMPDEST,
   pushAt 3711 2 9344,
   opAt 3712 .MLOAD,
   pushAt 3713 2 256,
   opAt 3714 .EQ,
   pushAt 3715 2 5026,
   opAt 3716 .JUMPI,
   opAt 3737 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1575 .JUMPDEST,
   pushAt 1576 2 4978,
   opAt 1577 .JUMP,
   opAt 3710 .JUMPDEST,
   pushAt 3711 2 9344,
   opAt 3712 .MLOAD,
   pushAt 3713 2 256,
   opAt 3714 .EQ,
   pushAt 3715 2 5026,
   opAt 3716 .JUMPI,
   pushAt 3717 2 9344,
   opAt 3718 .MLOAD,
   pushAt 3719 1 128,
   opAt 3720 .EQ,
   pushAt 3721 2 5312,
   opAt 3722 .JUMPI,
   opAt 3931 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3738 2 8480,
   opAt 3739 .MLOAD,
   pushAt 3740 1 224,
   opAt 3741 .MLOAD,
   opAt 3742 (.Dup ⟨1, by decide⟩),
   opAt 3743 (.Dup ⟨1, by decide⟩),
   opAt 3744 .GT,
   opAt 3745 (.Swap ⟨1, by decide⟩),
   opAt 3746 .SUB,
   pushAt 3747 2 7392,
   opAt 3748 .MSTORE]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3749 2 8448,
   opAt 3750 .MLOAD,
   pushAt 3751 1 192,
   opAt 3752 .MLOAD,
   opAt 3753 (.Dup ⟨1, by decide⟩),
   opAt 3754 (.Dup ⟨1, by decide⟩),
   opAt 3755 .GT,
   opAt 3756 (.Swap ⟨1, by decide⟩),
   opAt 3757 .SUB,
   opAt 3758 (.Dup ⟨2, by decide⟩),
   opAt 3759 (.Dup ⟨1, by decide⟩),
   opAt 3760 .SUB,
   opAt 3761 (.Swap ⟨2, by decide⟩),
   opAt 3762 .GT,
   opAt 3763 .OR,
   opAt 3764 (.Swap ⟨0, by decide⟩),
   pushAt 3765 2 7360,
   opAt 3766 .MSTORE]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3767 2 8416,
   opAt 3768 .MLOAD,
   pushAt 3769 1 160,
   opAt 3770 .MLOAD,
   opAt 3771 (.Dup ⟨1, by decide⟩),
   opAt 3772 (.Dup ⟨1, by decide⟩),
   opAt 3773 .GT,
   opAt 3774 (.Swap ⟨1, by decide⟩),
   opAt 3775 .SUB,
   opAt 3776 (.Dup ⟨2, by decide⟩),
   opAt 3777 (.Dup ⟨1, by decide⟩),
   opAt 3778 .SUB,
   opAt 3779 (.Swap ⟨2, by decide⟩),
   opAt 3780 .GT,
   opAt 3781 .OR,
   opAt 3782 (.Swap ⟨0, by decide⟩),
   pushAt 3783 2 7328,
   opAt 3784 .MSTORE]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3785 2 8384,
   opAt 3786 .MLOAD,
   pushAt 3787 1 128,
   opAt 3788 .MLOAD,
   opAt 3789 (.Dup ⟨1, by decide⟩),
   opAt 3790 (.Dup ⟨1, by decide⟩),
   opAt 3791 .GT,
   opAt 3792 (.Swap ⟨1, by decide⟩),
   opAt 3793 .SUB,
   opAt 3794 (.Dup ⟨2, by decide⟩),
   opAt 3795 (.Dup ⟨1, by decide⟩),
   opAt 3796 .SUB,
   opAt 3797 (.Swap ⟨2, by decide⟩),
   opAt 3798 .GT,
   opAt 3799 .OR,
   opAt 3800 (.Swap ⟨0, by decide⟩),
   pushAt 3801 2 7296,
   opAt 3802 .MSTORE]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3803 .JUMPDEST,
   pushAt 3804 2 8352,
   opAt 3805 .MLOAD,
   pushAt 3806 1 96,
   opAt 3807 .MLOAD,
   opAt 3808 (.Dup ⟨1, by decide⟩),
   opAt 3809 (.Dup ⟨1, by decide⟩),
   opAt 3810 .GT,
   opAt 3811 (.Swap ⟨1, by decide⟩),
   opAt 3812 .SUB,
   opAt 3813 (.Dup ⟨2, by decide⟩),
   opAt 3814 (.Dup ⟨1, by decide⟩),
   opAt 3815 .SUB,
   opAt 3816 (.Swap ⟨2, by decide⟩),
   opAt 3817 .GT,
   opAt 3818 .OR,
   opAt 3819 (.Swap ⟨0, by decide⟩),
   pushAt 3820 2 7264,
   opAt 3821 .MSTORE]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3822 .JUMPDEST,
   pushAt 3823 2 8320,
   opAt 3824 .MLOAD,
   pushAt 3825 1 64,
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
   pushAt 3839 2 7232,
   opAt 3840 .MSTORE]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3841 2 8288,
   opAt 3842 .MLOAD,
   pushAt 3843 1 32,
   opAt 3844 .MLOAD,
   opAt 3845 (.Dup ⟨1, by decide⟩),
   opAt 3846 (.Dup ⟨1, by decide⟩),
   opAt 3847 .GT,
   opAt 3848 (.Swap ⟨1, by decide⟩),
   opAt 3849 .SUB,
   opAt 3850 (.Dup ⟨2, by decide⟩),
   opAt 3851 (.Dup ⟨1, by decide⟩),
   opAt 3852 .SUB,
   opAt 3853 (.Swap ⟨2, by decide⟩),
   opAt 3854 .GT,
   opAt 3855 .OR,
   opAt 3856 (.Swap ⟨0, by decide⟩),
   pushAt 3857 2 7200,
   opAt 3858 .MSTORE]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3859 2 8256,
   opAt 3860 .MLOAD,
   pushAt 3861 0 0,
   opAt 3862 .MLOAD,
   opAt 3863 (.Dup ⟨1, by decide⟩),
   opAt 3864 (.Dup ⟨1, by decide⟩),
   opAt 3865 .GT,
   opAt 3866 (.Swap ⟨1, by decide⟩),
   opAt 3867 .SUB,
   opAt 3868 (.Dup ⟨2, by decide⟩),
   opAt 3869 (.Dup ⟨1, by decide⟩),
   opAt 3870 .SUB,
   opAt 3871 (.Swap ⟨2, by decide⟩),
   opAt 3872 .GT,
   opAt 3873 .OR,
   opAt 3874 (.Swap ⟨0, by decide⟩),
   pushAt 3875 2 7168,
   opAt 3876 .MSTORE]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3877 .ISZERO,
   pushAt 3878 2 8224,
   opAt 3879 .MLOAD,
   opAt 3880 .OR,
   pushAt 3881 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 3882 .MUL,
   pushAt 3883 2 8256,
   opAt 3884 .ADD,
   pushAt 3885 2 9344,
   opAt 3886 .MLOAD,
   opAt 3887 (.Swap ⟨1, by decide⟩),
   opAt 3888 .MCOPY,
   opAt 3889 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3932 2 8352,
   opAt 3933 .MLOAD,
   pushAt 3934 1 96,
   opAt 3935 .MLOAD,
   opAt 3936 (.Dup ⟨1, by decide⟩),
   opAt 3937 (.Dup ⟨1, by decide⟩),
   opAt 3938 .GT,
   opAt 3939 (.Swap ⟨1, by decide⟩),
   opAt 3940 .SUB,
   pushAt 3941 2 7264,
   opAt 3942 .MSTORE,
   pushAt 3943 2 5136,
   opAt 3944 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3822 .JUMPDEST,
   pushAt 3823 2 8320,
   opAt 3824 .MLOAD,
   pushAt 3825 1 64,
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
   pushAt 3839 2 7232,
   opAt 3840 .MSTORE]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3841 2 8288,
   opAt 3842 .MLOAD,
   pushAt 3843 1 32,
   opAt 3844 .MLOAD,
   opAt 3845 (.Dup ⟨1, by decide⟩),
   opAt 3846 (.Dup ⟨1, by decide⟩),
   opAt 3847 .GT,
   opAt 3848 (.Swap ⟨1, by decide⟩),
   opAt 3849 .SUB,
   opAt 3850 (.Dup ⟨2, by decide⟩),
   opAt 3851 (.Dup ⟨1, by decide⟩),
   opAt 3852 .SUB,
   opAt 3853 (.Swap ⟨2, by decide⟩),
   opAt 3854 .GT,
   opAt 3855 .OR,
   opAt 3856 (.Swap ⟨0, by decide⟩),
   pushAt 3857 2 7200,
   opAt 3858 .MSTORE]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3859 2 8256,
   opAt 3860 .MLOAD,
   pushAt 3861 0 0,
   opAt 3862 .MLOAD,
   opAt 3863 (.Dup ⟨1, by decide⟩),
   opAt 3864 (.Dup ⟨1, by decide⟩),
   opAt 3865 .GT,
   opAt 3866 (.Swap ⟨1, by decide⟩),
   opAt 3867 .SUB,
   opAt 3868 (.Dup ⟨2, by decide⟩),
   opAt 3869 (.Dup ⟨1, by decide⟩),
   opAt 3870 .SUB,
   opAt 3871 (.Swap ⟨2, by decide⟩),
   opAt 3872 .GT,
   opAt 3873 .OR,
   opAt 3874 (.Swap ⟨0, by decide⟩),
   pushAt 3875 2 7168,
   opAt 3876 .MSTORE]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3877 .ISZERO,
   pushAt 3878 2 8224,
   opAt 3879 .MLOAD,
   opAt 3880 .OR,
   pushAt 3881 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 3882 .MUL,
   pushAt 3883 2 8256,
   opAt 3884 .ADD,
   pushAt 3885 2 9344,
   opAt 3886 .MLOAD,
   opAt 3887 (.Swap ⟨1, by decide⟩),
   opAt 3888 .MCOPY,
   opAt 3889 .JUMP]

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
        Artifact.submissionArtifact.instructionPC 1576 + (YulEvmCompiler.Instr.push 2 4978).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1576 _ (by rfl)
    _ = 2143 := by rw [fixedPC1618]; rfl

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3710 = 4978 := by rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4978 = true := by
  simpa only [Artifact.instructionPC, fixedPC3777] using Artifact.isValidJumpDest_index 3710 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3711 = 4979 := by
  calc
    Artifact.submissionArtifact.instructionPC 3711 =
        Artifact.submissionArtifact.instructionPC 3710 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3710 _ (by rfl)
    _ = 4979 := by rw [fixedPC3777]; rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3712 = 4982 := by
  calc
    Artifact.submissionArtifact.instructionPC 3712 =
        Artifact.submissionArtifact.instructionPC 3711 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3711 _ (by rfl)
    _ = 4982 := by rw [fixedPC3778]; rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3713 = 4983 := by
  calc
    Artifact.submissionArtifact.instructionPC 3713 =
        Artifact.submissionArtifact.instructionPC 3712 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3712 _ (by rfl)
    _ = 4983 := by rw [fixedPC3779]; rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3714 = 4986 := by
  calc
    Artifact.submissionArtifact.instructionPC 3714 =
        Artifact.submissionArtifact.instructionPC 3713 + (YulEvmCompiler.Instr.push 2 256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3713 _ (by rfl)
    _ = 4986 := by rw [fixedPC3780]; rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3715 = 4987 := by
  calc
    Artifact.submissionArtifact.instructionPC 3715 =
        Artifact.submissionArtifact.instructionPC 3714 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3714 _ (by rfl)
    _ = 4987 := by rw [fixedPC3781]; rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3716 = 4990 := by
  calc
    Artifact.submissionArtifact.instructionPC 3716 =
        Artifact.submissionArtifact.instructionPC 3715 + (YulEvmCompiler.Instr.push 2 5026).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3715 _ (by rfl)
    _ = 4990 := by rw [fixedPC3782]; rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3717 = 4991 := by
  calc
    Artifact.submissionArtifact.instructionPC 3717 =
        Artifact.submissionArtifact.instructionPC 3716 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3716 _ (by rfl)
    _ = 4991 := by rw [fixedPC3783]; rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3718 = 4994 := by
  calc
    Artifact.submissionArtifact.instructionPC 3718 =
        Artifact.submissionArtifact.instructionPC 3717 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3717 _ (by rfl)
    _ = 4994 := by rw [fixedPC3784]; rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3719 = 4995 := by
  calc
    Artifact.submissionArtifact.instructionPC 3719 =
        Artifact.submissionArtifact.instructionPC 3718 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3718 _ (by rfl)
    _ = 4995 := by rw [fixedPC3785]; rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3720 = 4997 := by
  calc
    Artifact.submissionArtifact.instructionPC 3720 =
        Artifact.submissionArtifact.instructionPC 3719 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3719 _ (by rfl)
    _ = 4997 := by rw [fixedPC3786]; rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3721 = 4998 := by
  calc
    Artifact.submissionArtifact.instructionPC 3721 =
        Artifact.submissionArtifact.instructionPC 3720 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3720 _ (by rfl)
    _ = 4998 := by rw [fixedPC3787]; rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3722 = 5001 := by
  calc
    Artifact.submissionArtifact.instructionPC 3722 =
        Artifact.submissionArtifact.instructionPC 3721 + (YulEvmCompiler.Instr.push 2 5312).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3721 _ (by rfl)
    _ = 5001 := by rw [fixedPC3788]; rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3723 = 5002 := by
  calc
    Artifact.submissionArtifact.instructionPC 3723 =
        Artifact.submissionArtifact.instructionPC 3722 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3722 _ (by rfl)
    _ = 5002 := by rw [fixedPC3789]; rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3724 = 5005 := by
  calc
    Artifact.submissionArtifact.instructionPC 3724 =
        Artifact.submissionArtifact.instructionPC 3723 + (YulEvmCompiler.Instr.push 2 9440).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3723 _ (by rfl)
    _ = 5005 := by rw [fixedPC3790]; rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3725 = 5006 := by
  calc
    Artifact.submissionArtifact.instructionPC 3725 =
        Artifact.submissionArtifact.instructionPC 3724 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3724 _ (by rfl)
    _ = 5006 := by rw [fixedPC3791]; rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3726 = 5009 := by
  calc
    Artifact.submissionArtifact.instructionPC 3726 =
        Artifact.submissionArtifact.instructionPC 3725 + (YulEvmCompiler.Instr.push 2 9408).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3725 _ (by rfl)
    _ = 5009 := by rw [fixedPC3792]; rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3727 = 5010 := by
  calc
    Artifact.submissionArtifact.instructionPC 3727 =
        Artifact.submissionArtifact.instructionPC 3726 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3726 _ (by rfl)
    _ = 5010 := by rw [fixedPC3793]; rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3728 = 5011 := by
  calc
    Artifact.submissionArtifact.instructionPC 3728 =
        Artifact.submissionArtifact.instructionPC 3727 + (YulEvmCompiler.Instr.op (.Dup ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3727 _ (by rfl)
    _ = 5011 := by rw [fixedPC3794]; rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3729 = 5014 := by
  calc
    Artifact.submissionArtifact.instructionPC 3729 =
        Artifact.submissionArtifact.instructionPC 3728 + (YulEvmCompiler.Instr.push 2 7168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3728 _ (by rfl)
    _ = 5014 := by rw [fixedPC3795]; rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3730 = 5015 := by
  calc
    Artifact.submissionArtifact.instructionPC 3730 =
        Artifact.submissionArtifact.instructionPC 3729 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3729 _ (by rfl)
    _ = 5015 := by rw [fixedPC3796]; rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3731 = 5018 := by
  calc
    Artifact.submissionArtifact.instructionPC 3731 =
        Artifact.submissionArtifact.instructionPC 3730 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3730 _ (by rfl)
    _ = 5018 := by rw [fixedPC3797]; rfl

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3732 = 5019 := by
  calc
    Artifact.submissionArtifact.instructionPC 3732 =
        Artifact.submissionArtifact.instructionPC 3731 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3731 _ (by rfl)
    _ = 5019 := by rw [fixedPC3798]; rfl

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3733 = 5020 := by
  calc
    Artifact.submissionArtifact.instructionPC 3733 =
        Artifact.submissionArtifact.instructionPC 3732 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3732 _ (by rfl)
    _ = 5020 := by rw [fixedPC3799]; rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3734 = 5021 := by
  calc
    Artifact.submissionArtifact.instructionPC 3734 =
        Artifact.submissionArtifact.instructionPC 3733 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3733 _ (by rfl)
    _ = 5021 := by rw [fixedPC3800]; rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3735 = 5022 := by
  calc
    Artifact.submissionArtifact.instructionPC 3735 =
        Artifact.submissionArtifact.instructionPC 3734 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3734 _ (by rfl)
    _ = 5022 := by rw [fixedPC3801]; rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3736 = 5025 := by
  calc
    Artifact.submissionArtifact.instructionPC 3736 =
        Artifact.submissionArtifact.instructionPC 3735 + (YulEvmCompiler.Instr.push 2 2144).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3735 _ (by rfl)
    _ = 5025 := by rw [fixedPC3802]; rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3737 = 5026 := by
  calc
    Artifact.submissionArtifact.instructionPC 3737 =
        Artifact.submissionArtifact.instructionPC 3736 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3736 _ (by rfl)
    _ = 5026 := by rw [fixedPC3803]; rfl

@[simp] theorem fixedJump5023 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5026 = true := by
  simpa only [Artifact.instructionPC, fixedPC3804] using Artifact.isValidJumpDest_index 3737 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3738 = 5027 := by
  calc
    Artifact.submissionArtifact.instructionPC 3738 =
        Artifact.submissionArtifact.instructionPC 3737 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3737 _ (by rfl)
    _ = 5027 := by rw [fixedPC3804]; rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3739 = 5030 := by
  calc
    Artifact.submissionArtifact.instructionPC 3739 =
        Artifact.submissionArtifact.instructionPC 3738 + (YulEvmCompiler.Instr.push 2 8480).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3738 _ (by rfl)
    _ = 5030 := by rw [fixedPC3805]; rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3740 = 5031 := by
  calc
    Artifact.submissionArtifact.instructionPC 3740 =
        Artifact.submissionArtifact.instructionPC 3739 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3739 _ (by rfl)
    _ = 5031 := by rw [fixedPC3806]; rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3741 = 5033 := by
  calc
    Artifact.submissionArtifact.instructionPC 3741 =
        Artifact.submissionArtifact.instructionPC 3740 + (YulEvmCompiler.Instr.push 1 224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3740 _ (by rfl)
    _ = 5033 := by rw [fixedPC3807]; rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3742 = 5034 := by
  calc
    Artifact.submissionArtifact.instructionPC 3742 =
        Artifact.submissionArtifact.instructionPC 3741 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3741 _ (by rfl)
    _ = 5034 := by rw [fixedPC3808]; rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3743 = 5035 := by
  calc
    Artifact.submissionArtifact.instructionPC 3743 =
        Artifact.submissionArtifact.instructionPC 3742 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3742 _ (by rfl)
    _ = 5035 := by rw [fixedPC3809]; rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3744 = 5036 := by
  calc
    Artifact.submissionArtifact.instructionPC 3744 =
        Artifact.submissionArtifact.instructionPC 3743 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3743 _ (by rfl)
    _ = 5036 := by rw [fixedPC3810]; rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3745 = 5037 := by
  calc
    Artifact.submissionArtifact.instructionPC 3745 =
        Artifact.submissionArtifact.instructionPC 3744 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3744 _ (by rfl)
    _ = 5037 := by rw [fixedPC3811]; rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3746 = 5038 := by
  calc
    Artifact.submissionArtifact.instructionPC 3746 =
        Artifact.submissionArtifact.instructionPC 3745 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3745 _ (by rfl)
    _ = 5038 := by rw [fixedPC3812]; rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3747 = 5039 := by
  calc
    Artifact.submissionArtifact.instructionPC 3747 =
        Artifact.submissionArtifact.instructionPC 3746 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3746 _ (by rfl)
    _ = 5039 := by rw [fixedPC3813]; rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3748 = 5042 := by
  calc
    Artifact.submissionArtifact.instructionPC 3748 =
        Artifact.submissionArtifact.instructionPC 3747 + (YulEvmCompiler.Instr.push 2 7392).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3747 _ (by rfl)
    _ = 5042 := by rw [fixedPC3814]; rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3749 = 5043 := by
  calc
    Artifact.submissionArtifact.instructionPC 3749 =
        Artifact.submissionArtifact.instructionPC 3748 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3748 _ (by rfl)
    _ = 5043 := by rw [fixedPC3815]; rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3750 = 5046 := by
  calc
    Artifact.submissionArtifact.instructionPC 3750 =
        Artifact.submissionArtifact.instructionPC 3749 + (YulEvmCompiler.Instr.push 2 8448).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3749 _ (by rfl)
    _ = 5046 := by rw [fixedPC3816]; rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3751 = 5047 := by
  calc
    Artifact.submissionArtifact.instructionPC 3751 =
        Artifact.submissionArtifact.instructionPC 3750 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3750 _ (by rfl)
    _ = 5047 := by rw [fixedPC3817]; rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3752 = 5049 := by
  calc
    Artifact.submissionArtifact.instructionPC 3752 =
        Artifact.submissionArtifact.instructionPC 3751 + (YulEvmCompiler.Instr.push 1 192).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3751 _ (by rfl)
    _ = 5049 := by rw [fixedPC3818]; rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3753 = 5050 := by
  calc
    Artifact.submissionArtifact.instructionPC 3753 =
        Artifact.submissionArtifact.instructionPC 3752 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3752 _ (by rfl)
    _ = 5050 := by rw [fixedPC3819]; rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3754 = 5051 := by
  calc
    Artifact.submissionArtifact.instructionPC 3754 =
        Artifact.submissionArtifact.instructionPC 3753 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3753 _ (by rfl)
    _ = 5051 := by rw [fixedPC3820]; rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3755 = 5052 := by
  calc
    Artifact.submissionArtifact.instructionPC 3755 =
        Artifact.submissionArtifact.instructionPC 3754 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3754 _ (by rfl)
    _ = 5052 := by rw [fixedPC3821]; rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3756 = 5053 := by
  calc
    Artifact.submissionArtifact.instructionPC 3756 =
        Artifact.submissionArtifact.instructionPC 3755 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3755 _ (by rfl)
    _ = 5053 := by rw [fixedPC3822]; rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3757 = 5054 := by
  calc
    Artifact.submissionArtifact.instructionPC 3757 =
        Artifact.submissionArtifact.instructionPC 3756 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3756 _ (by rfl)
    _ = 5054 := by rw [fixedPC3823]; rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3758 = 5055 := by
  calc
    Artifact.submissionArtifact.instructionPC 3758 =
        Artifact.submissionArtifact.instructionPC 3757 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3757 _ (by rfl)
    _ = 5055 := by rw [fixedPC3824]; rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3759 = 5056 := by
  calc
    Artifact.submissionArtifact.instructionPC 3759 =
        Artifact.submissionArtifact.instructionPC 3758 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3758 _ (by rfl)
    _ = 5056 := by rw [fixedPC3825]; rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3760 = 5057 := by
  calc
    Artifact.submissionArtifact.instructionPC 3760 =
        Artifact.submissionArtifact.instructionPC 3759 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3759 _ (by rfl)
    _ = 5057 := by rw [fixedPC3826]; rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3761 = 5058 := by
  calc
    Artifact.submissionArtifact.instructionPC 3761 =
        Artifact.submissionArtifact.instructionPC 3760 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3760 _ (by rfl)
    _ = 5058 := by rw [fixedPC3827]; rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3762 = 5059 := by
  calc
    Artifact.submissionArtifact.instructionPC 3762 =
        Artifact.submissionArtifact.instructionPC 3761 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3761 _ (by rfl)
    _ = 5059 := by rw [fixedPC3828]; rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3763 = 5060 := by
  calc
    Artifact.submissionArtifact.instructionPC 3763 =
        Artifact.submissionArtifact.instructionPC 3762 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3762 _ (by rfl)
    _ = 5060 := by rw [fixedPC3829]; rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3764 = 5061 := by
  calc
    Artifact.submissionArtifact.instructionPC 3764 =
        Artifact.submissionArtifact.instructionPC 3763 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3763 _ (by rfl)
    _ = 5061 := by rw [fixedPC3830]; rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3765 = 5062 := by
  calc
    Artifact.submissionArtifact.instructionPC 3765 =
        Artifact.submissionArtifact.instructionPC 3764 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3764 _ (by rfl)
    _ = 5062 := by rw [fixedPC3831]; rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3766 = 5065 := by
  calc
    Artifact.submissionArtifact.instructionPC 3766 =
        Artifact.submissionArtifact.instructionPC 3765 + (YulEvmCompiler.Instr.push 2 7360).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3765 _ (by rfl)
    _ = 5065 := by rw [fixedPC3832]; rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3767 = 5066 := by
  calc
    Artifact.submissionArtifact.instructionPC 3767 =
        Artifact.submissionArtifact.instructionPC 3766 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3766 _ (by rfl)
    _ = 5066 := by rw [fixedPC3833]; rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3768 = 5069 := by
  calc
    Artifact.submissionArtifact.instructionPC 3768 =
        Artifact.submissionArtifact.instructionPC 3767 + (YulEvmCompiler.Instr.push 2 8416).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3767 _ (by rfl)
    _ = 5069 := by rw [fixedPC3834]; rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3769 = 5070 := by
  calc
    Artifact.submissionArtifact.instructionPC 3769 =
        Artifact.submissionArtifact.instructionPC 3768 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3768 _ (by rfl)
    _ = 5070 := by rw [fixedPC3835]; rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3770 = 5072 := by
  calc
    Artifact.submissionArtifact.instructionPC 3770 =
        Artifact.submissionArtifact.instructionPC 3769 + (YulEvmCompiler.Instr.push 1 160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3769 _ (by rfl)
    _ = 5072 := by rw [fixedPC3836]; rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3771 = 5073 := by
  calc
    Artifact.submissionArtifact.instructionPC 3771 =
        Artifact.submissionArtifact.instructionPC 3770 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3770 _ (by rfl)
    _ = 5073 := by rw [fixedPC3837]; rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3772 = 5074 := by
  calc
    Artifact.submissionArtifact.instructionPC 3772 =
        Artifact.submissionArtifact.instructionPC 3771 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3771 _ (by rfl)
    _ = 5074 := by rw [fixedPC3838]; rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3773 = 5075 := by
  calc
    Artifact.submissionArtifact.instructionPC 3773 =
        Artifact.submissionArtifact.instructionPC 3772 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3772 _ (by rfl)
    _ = 5075 := by rw [fixedPC3839]; rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3774 = 5076 := by
  calc
    Artifact.submissionArtifact.instructionPC 3774 =
        Artifact.submissionArtifact.instructionPC 3773 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3773 _ (by rfl)
    _ = 5076 := by rw [fixedPC3840]; rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3775 = 5077 := by
  calc
    Artifact.submissionArtifact.instructionPC 3775 =
        Artifact.submissionArtifact.instructionPC 3774 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3774 _ (by rfl)
    _ = 5077 := by rw [fixedPC3841]; rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3776 = 5078 := by
  calc
    Artifact.submissionArtifact.instructionPC 3776 =
        Artifact.submissionArtifact.instructionPC 3775 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3775 _ (by rfl)
    _ = 5078 := by rw [fixedPC3842]; rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3777 = 5079 := by
  calc
    Artifact.submissionArtifact.instructionPC 3777 =
        Artifact.submissionArtifact.instructionPC 3776 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3776 _ (by rfl)
    _ = 5079 := by rw [fixedPC3843]; rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3778 = 5080 := by
  calc
    Artifact.submissionArtifact.instructionPC 3778 =
        Artifact.submissionArtifact.instructionPC 3777 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3777 _ (by rfl)
    _ = 5080 := by rw [fixedPC3844]; rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3779 = 5081 := by
  calc
    Artifact.submissionArtifact.instructionPC 3779 =
        Artifact.submissionArtifact.instructionPC 3778 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3778 _ (by rfl)
    _ = 5081 := by rw [fixedPC3845]; rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3780 = 5082 := by
  calc
    Artifact.submissionArtifact.instructionPC 3780 =
        Artifact.submissionArtifact.instructionPC 3779 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3779 _ (by rfl)
    _ = 5082 := by rw [fixedPC3846]; rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3781 = 5083 := by
  calc
    Artifact.submissionArtifact.instructionPC 3781 =
        Artifact.submissionArtifact.instructionPC 3780 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3780 _ (by rfl)
    _ = 5083 := by rw [fixedPC3847]; rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3782 = 5084 := by
  calc
    Artifact.submissionArtifact.instructionPC 3782 =
        Artifact.submissionArtifact.instructionPC 3781 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3781 _ (by rfl)
    _ = 5084 := by rw [fixedPC3848]; rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3783 = 5085 := by
  calc
    Artifact.submissionArtifact.instructionPC 3783 =
        Artifact.submissionArtifact.instructionPC 3782 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3782 _ (by rfl)
    _ = 5085 := by rw [fixedPC3849]; rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3784 = 5088 := by
  calc
    Artifact.submissionArtifact.instructionPC 3784 =
        Artifact.submissionArtifact.instructionPC 3783 + (YulEvmCompiler.Instr.push 2 7328).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3783 _ (by rfl)
    _ = 5088 := by rw [fixedPC3850]; rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3785 = 5089 := by
  calc
    Artifact.submissionArtifact.instructionPC 3785 =
        Artifact.submissionArtifact.instructionPC 3784 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3784 _ (by rfl)
    _ = 5089 := by rw [fixedPC3851]; rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3786 = 5092 := by
  calc
    Artifact.submissionArtifact.instructionPC 3786 =
        Artifact.submissionArtifact.instructionPC 3785 + (YulEvmCompiler.Instr.push 2 8384).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3785 _ (by rfl)
    _ = 5092 := by rw [fixedPC3852]; rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3787 = 5093 := by
  calc
    Artifact.submissionArtifact.instructionPC 3787 =
        Artifact.submissionArtifact.instructionPC 3786 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3786 _ (by rfl)
    _ = 5093 := by rw [fixedPC3853]; rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3788 = 5095 := by
  calc
    Artifact.submissionArtifact.instructionPC 3788 =
        Artifact.submissionArtifact.instructionPC 3787 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3787 _ (by rfl)
    _ = 5095 := by rw [fixedPC3854]; rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3789 = 5096 := by
  calc
    Artifact.submissionArtifact.instructionPC 3789 =
        Artifact.submissionArtifact.instructionPC 3788 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3788 _ (by rfl)
    _ = 5096 := by rw [fixedPC3855]; rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3790 = 5097 := by
  calc
    Artifact.submissionArtifact.instructionPC 3790 =
        Artifact.submissionArtifact.instructionPC 3789 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3789 _ (by rfl)
    _ = 5097 := by rw [fixedPC3856]; rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3791 = 5098 := by
  calc
    Artifact.submissionArtifact.instructionPC 3791 =
        Artifact.submissionArtifact.instructionPC 3790 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3790 _ (by rfl)
    _ = 5098 := by rw [fixedPC3857]; rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3792 = 5099 := by
  calc
    Artifact.submissionArtifact.instructionPC 3792 =
        Artifact.submissionArtifact.instructionPC 3791 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3791 _ (by rfl)
    _ = 5099 := by rw [fixedPC3858]; rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3793 = 5100 := by
  calc
    Artifact.submissionArtifact.instructionPC 3793 =
        Artifact.submissionArtifact.instructionPC 3792 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3792 _ (by rfl)
    _ = 5100 := by rw [fixedPC3859]; rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3794 = 5101 := by
  calc
    Artifact.submissionArtifact.instructionPC 3794 =
        Artifact.submissionArtifact.instructionPC 3793 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3793 _ (by rfl)
    _ = 5101 := by rw [fixedPC3860]; rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3795 = 5102 := by
  calc
    Artifact.submissionArtifact.instructionPC 3795 =
        Artifact.submissionArtifact.instructionPC 3794 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3794 _ (by rfl)
    _ = 5102 := by rw [fixedPC3861]; rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3796 = 5103 := by
  calc
    Artifact.submissionArtifact.instructionPC 3796 =
        Artifact.submissionArtifact.instructionPC 3795 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3795 _ (by rfl)
    _ = 5103 := by rw [fixedPC3862]; rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3797 = 5104 := by
  calc
    Artifact.submissionArtifact.instructionPC 3797 =
        Artifact.submissionArtifact.instructionPC 3796 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3796 _ (by rfl)
    _ = 5104 := by rw [fixedPC3863]; rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3798 = 5105 := by
  calc
    Artifact.submissionArtifact.instructionPC 3798 =
        Artifact.submissionArtifact.instructionPC 3797 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3797 _ (by rfl)
    _ = 5105 := by rw [fixedPC3864]; rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3799 = 5106 := by
  calc
    Artifact.submissionArtifact.instructionPC 3799 =
        Artifact.submissionArtifact.instructionPC 3798 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3798 _ (by rfl)
    _ = 5106 := by rw [fixedPC3865]; rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3800 = 5107 := by
  calc
    Artifact.submissionArtifact.instructionPC 3800 =
        Artifact.submissionArtifact.instructionPC 3799 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3799 _ (by rfl)
    _ = 5107 := by rw [fixedPC3866]; rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3801 = 5108 := by
  calc
    Artifact.submissionArtifact.instructionPC 3801 =
        Artifact.submissionArtifact.instructionPC 3800 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3800 _ (by rfl)
    _ = 5108 := by rw [fixedPC3867]; rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3802 = 5111 := by
  calc
    Artifact.submissionArtifact.instructionPC 3802 =
        Artifact.submissionArtifact.instructionPC 3801 + (YulEvmCompiler.Instr.push 2 7296).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3801 _ (by rfl)
    _ = 5111 := by rw [fixedPC3868]; rfl

@[simp] theorem fixedPC3870 : Artifact.submissionArtifact.instructionPC 3803 = 5112 := by
  calc
    Artifact.submissionArtifact.instructionPC 3803 =
        Artifact.submissionArtifact.instructionPC 3802 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3802 _ (by rfl)
    _ = 5112 := by rw [fixedPC3869]; rfl

@[simp] theorem fixedJump5109 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5112 = true := by
  simpa only [Artifact.instructionPC, fixedPC3870] using Artifact.isValidJumpDest_index 3803 (by rfl)

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3804 = 5113 := by
  calc
    Artifact.submissionArtifact.instructionPC 3804 =
        Artifact.submissionArtifact.instructionPC 3803 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3803 _ (by rfl)
    _ = 5113 := by rw [fixedPC3870]; rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3805 = 5116 := by
  calc
    Artifact.submissionArtifact.instructionPC 3805 =
        Artifact.submissionArtifact.instructionPC 3804 + (YulEvmCompiler.Instr.push 2 8352).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3804 _ (by rfl)
    _ = 5116 := by rw [fixedPC3871]; rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3806 = 5117 := by
  calc
    Artifact.submissionArtifact.instructionPC 3806 =
        Artifact.submissionArtifact.instructionPC 3805 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3805 _ (by rfl)
    _ = 5117 := by rw [fixedPC3872]; rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3807 = 5119 := by
  calc
    Artifact.submissionArtifact.instructionPC 3807 =
        Artifact.submissionArtifact.instructionPC 3806 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3806 _ (by rfl)
    _ = 5119 := by rw [fixedPC3873]; rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3808 = 5120 := by
  calc
    Artifact.submissionArtifact.instructionPC 3808 =
        Artifact.submissionArtifact.instructionPC 3807 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3807 _ (by rfl)
    _ = 5120 := by rw [fixedPC3874]; rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3809 = 5121 := by
  calc
    Artifact.submissionArtifact.instructionPC 3809 =
        Artifact.submissionArtifact.instructionPC 3808 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3808 _ (by rfl)
    _ = 5121 := by rw [fixedPC3875]; rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3810 = 5122 := by
  calc
    Artifact.submissionArtifact.instructionPC 3810 =
        Artifact.submissionArtifact.instructionPC 3809 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3809 _ (by rfl)
    _ = 5122 := by rw [fixedPC3876]; rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3811 = 5123 := by
  calc
    Artifact.submissionArtifact.instructionPC 3811 =
        Artifact.submissionArtifact.instructionPC 3810 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3810 _ (by rfl)
    _ = 5123 := by rw [fixedPC3877]; rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3812 = 5124 := by
  calc
    Artifact.submissionArtifact.instructionPC 3812 =
        Artifact.submissionArtifact.instructionPC 3811 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3811 _ (by rfl)
    _ = 5124 := by rw [fixedPC3878]; rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3813 = 5125 := by
  calc
    Artifact.submissionArtifact.instructionPC 3813 =
        Artifact.submissionArtifact.instructionPC 3812 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3812 _ (by rfl)
    _ = 5125 := by rw [fixedPC3879]; rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3814 = 5126 := by
  calc
    Artifact.submissionArtifact.instructionPC 3814 =
        Artifact.submissionArtifact.instructionPC 3813 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3813 _ (by rfl)
    _ = 5126 := by rw [fixedPC3880]; rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3815 = 5127 := by
  calc
    Artifact.submissionArtifact.instructionPC 3815 =
        Artifact.submissionArtifact.instructionPC 3814 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3814 _ (by rfl)
    _ = 5127 := by rw [fixedPC3881]; rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3816 = 5128 := by
  calc
    Artifact.submissionArtifact.instructionPC 3816 =
        Artifact.submissionArtifact.instructionPC 3815 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3815 _ (by rfl)
    _ = 5128 := by rw [fixedPC3882]; rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3817 = 5129 := by
  calc
    Artifact.submissionArtifact.instructionPC 3817 =
        Artifact.submissionArtifact.instructionPC 3816 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3816 _ (by rfl)
    _ = 5129 := by rw [fixedPC3883]; rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3818 = 5130 := by
  calc
    Artifact.submissionArtifact.instructionPC 3818 =
        Artifact.submissionArtifact.instructionPC 3817 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3817 _ (by rfl)
    _ = 5130 := by rw [fixedPC3884]; rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3819 = 5131 := by
  calc
    Artifact.submissionArtifact.instructionPC 3819 =
        Artifact.submissionArtifact.instructionPC 3818 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3818 _ (by rfl)
    _ = 5131 := by rw [fixedPC3885]; rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3820 = 5132 := by
  calc
    Artifact.submissionArtifact.instructionPC 3820 =
        Artifact.submissionArtifact.instructionPC 3819 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3819 _ (by rfl)
    _ = 5132 := by rw [fixedPC3886]; rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3821 = 5135 := by
  calc
    Artifact.submissionArtifact.instructionPC 3821 =
        Artifact.submissionArtifact.instructionPC 3820 + (YulEvmCompiler.Instr.push 2 7264).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3820 _ (by rfl)
    _ = 5135 := by rw [fixedPC3887]; rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3822 = 5136 := by
  calc
    Artifact.submissionArtifact.instructionPC 3822 =
        Artifact.submissionArtifact.instructionPC 3821 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3821 _ (by rfl)
    _ = 5136 := by rw [fixedPC3888]; rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5136 = true := by
  simpa only [Artifact.instructionPC, fixedPC3889] using Artifact.isValidJumpDest_index 3822 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3823 = 5137 := by
  calc
    Artifact.submissionArtifact.instructionPC 3823 =
        Artifact.submissionArtifact.instructionPC 3822 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3822 _ (by rfl)
    _ = 5137 := by rw [fixedPC3889]; rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3824 = 5140 := by
  calc
    Artifact.submissionArtifact.instructionPC 3824 =
        Artifact.submissionArtifact.instructionPC 3823 + (YulEvmCompiler.Instr.push 2 8320).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3823 _ (by rfl)
    _ = 5140 := by rw [fixedPC3890]; rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3825 = 5141 := by
  calc
    Artifact.submissionArtifact.instructionPC 3825 =
        Artifact.submissionArtifact.instructionPC 3824 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3824 _ (by rfl)
    _ = 5141 := by rw [fixedPC3891]; rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3826 = 5143 := by
  calc
    Artifact.submissionArtifact.instructionPC 3826 =
        Artifact.submissionArtifact.instructionPC 3825 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3825 _ (by rfl)
    _ = 5143 := by rw [fixedPC3892]; rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3827 = 5144 := by
  calc
    Artifact.submissionArtifact.instructionPC 3827 =
        Artifact.submissionArtifact.instructionPC 3826 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3826 _ (by rfl)
    _ = 5144 := by rw [fixedPC3893]; rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3828 = 5145 := by
  calc
    Artifact.submissionArtifact.instructionPC 3828 =
        Artifact.submissionArtifact.instructionPC 3827 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3827 _ (by rfl)
    _ = 5145 := by rw [fixedPC3894]; rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3829 = 5146 := by
  calc
    Artifact.submissionArtifact.instructionPC 3829 =
        Artifact.submissionArtifact.instructionPC 3828 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3828 _ (by rfl)
    _ = 5146 := by rw [fixedPC3895]; rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3830 = 5147 := by
  calc
    Artifact.submissionArtifact.instructionPC 3830 =
        Artifact.submissionArtifact.instructionPC 3829 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3829 _ (by rfl)
    _ = 5147 := by rw [fixedPC3896]; rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3831 = 5148 := by
  calc
    Artifact.submissionArtifact.instructionPC 3831 =
        Artifact.submissionArtifact.instructionPC 3830 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3830 _ (by rfl)
    _ = 5148 := by rw [fixedPC3897]; rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3832 = 5149 := by
  calc
    Artifact.submissionArtifact.instructionPC 3832 =
        Artifact.submissionArtifact.instructionPC 3831 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3831 _ (by rfl)
    _ = 5149 := by rw [fixedPC3898]; rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3833 = 5150 := by
  calc
    Artifact.submissionArtifact.instructionPC 3833 =
        Artifact.submissionArtifact.instructionPC 3832 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3832 _ (by rfl)
    _ = 5150 := by rw [fixedPC3899]; rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3834 = 5151 := by
  calc
    Artifact.submissionArtifact.instructionPC 3834 =
        Artifact.submissionArtifact.instructionPC 3833 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3833 _ (by rfl)
    _ = 5151 := by rw [fixedPC3900]; rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3835 = 5152 := by
  calc
    Artifact.submissionArtifact.instructionPC 3835 =
        Artifact.submissionArtifact.instructionPC 3834 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3834 _ (by rfl)
    _ = 5152 := by rw [fixedPC3901]; rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3836 = 5153 := by
  calc
    Artifact.submissionArtifact.instructionPC 3836 =
        Artifact.submissionArtifact.instructionPC 3835 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3835 _ (by rfl)
    _ = 5153 := by rw [fixedPC3902]; rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3837 = 5154 := by
  calc
    Artifact.submissionArtifact.instructionPC 3837 =
        Artifact.submissionArtifact.instructionPC 3836 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3836 _ (by rfl)
    _ = 5154 := by rw [fixedPC3903]; rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3838 = 5155 := by
  calc
    Artifact.submissionArtifact.instructionPC 3838 =
        Artifact.submissionArtifact.instructionPC 3837 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3837 _ (by rfl)
    _ = 5155 := by rw [fixedPC3904]; rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3839 = 5156 := by
  calc
    Artifact.submissionArtifact.instructionPC 3839 =
        Artifact.submissionArtifact.instructionPC 3838 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3838 _ (by rfl)
    _ = 5156 := by rw [fixedPC3905]; rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3840 = 5159 := by
  calc
    Artifact.submissionArtifact.instructionPC 3840 =
        Artifact.submissionArtifact.instructionPC 3839 + (YulEvmCompiler.Instr.push 2 7232).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3839 _ (by rfl)
    _ = 5159 := by rw [fixedPC3906]; rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3841 = 5160 := by
  calc
    Artifact.submissionArtifact.instructionPC 3841 =
        Artifact.submissionArtifact.instructionPC 3840 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3840 _ (by rfl)
    _ = 5160 := by rw [fixedPC3907]; rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3842 = 5163 := by
  calc
    Artifact.submissionArtifact.instructionPC 3842 =
        Artifact.submissionArtifact.instructionPC 3841 + (YulEvmCompiler.Instr.push 2 8288).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3841 _ (by rfl)
    _ = 5163 := by rw [fixedPC3908]; rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3843 = 5164 := by
  calc
    Artifact.submissionArtifact.instructionPC 3843 =
        Artifact.submissionArtifact.instructionPC 3842 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3842 _ (by rfl)
    _ = 5164 := by rw [fixedPC3909]; rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3844 = 5166 := by
  calc
    Artifact.submissionArtifact.instructionPC 3844 =
        Artifact.submissionArtifact.instructionPC 3843 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3843 _ (by rfl)
    _ = 5166 := by rw [fixedPC3910]; rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3845 = 5167 := by
  calc
    Artifact.submissionArtifact.instructionPC 3845 =
        Artifact.submissionArtifact.instructionPC 3844 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3844 _ (by rfl)
    _ = 5167 := by rw [fixedPC3911]; rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3846 = 5168 := by
  calc
    Artifact.submissionArtifact.instructionPC 3846 =
        Artifact.submissionArtifact.instructionPC 3845 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3845 _ (by rfl)
    _ = 5168 := by rw [fixedPC3912]; rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3847 = 5169 := by
  calc
    Artifact.submissionArtifact.instructionPC 3847 =
        Artifact.submissionArtifact.instructionPC 3846 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3846 _ (by rfl)
    _ = 5169 := by rw [fixedPC3913]; rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3848 = 5170 := by
  calc
    Artifact.submissionArtifact.instructionPC 3848 =
        Artifact.submissionArtifact.instructionPC 3847 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3847 _ (by rfl)
    _ = 5170 := by rw [fixedPC3914]; rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3849 = 5171 := by
  calc
    Artifact.submissionArtifact.instructionPC 3849 =
        Artifact.submissionArtifact.instructionPC 3848 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3848 _ (by rfl)
    _ = 5171 := by rw [fixedPC3915]; rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3850 = 5172 := by
  calc
    Artifact.submissionArtifact.instructionPC 3850 =
        Artifact.submissionArtifact.instructionPC 3849 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3849 _ (by rfl)
    _ = 5172 := by rw [fixedPC3916]; rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3851 = 5173 := by
  calc
    Artifact.submissionArtifact.instructionPC 3851 =
        Artifact.submissionArtifact.instructionPC 3850 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3850 _ (by rfl)
    _ = 5173 := by rw [fixedPC3917]; rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3852 = 5174 := by
  calc
    Artifact.submissionArtifact.instructionPC 3852 =
        Artifact.submissionArtifact.instructionPC 3851 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3851 _ (by rfl)
    _ = 5174 := by rw [fixedPC3918]; rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3853 = 5175 := by
  calc
    Artifact.submissionArtifact.instructionPC 3853 =
        Artifact.submissionArtifact.instructionPC 3852 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3852 _ (by rfl)
    _ = 5175 := by rw [fixedPC3919]; rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3854 = 5176 := by
  calc
    Artifact.submissionArtifact.instructionPC 3854 =
        Artifact.submissionArtifact.instructionPC 3853 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3853 _ (by rfl)
    _ = 5176 := by rw [fixedPC3920]; rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3855 = 5177 := by
  calc
    Artifact.submissionArtifact.instructionPC 3855 =
        Artifact.submissionArtifact.instructionPC 3854 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3854 _ (by rfl)
    _ = 5177 := by rw [fixedPC3921]; rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3856 = 5178 := by
  calc
    Artifact.submissionArtifact.instructionPC 3856 =
        Artifact.submissionArtifact.instructionPC 3855 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3855 _ (by rfl)
    _ = 5178 := by rw [fixedPC3922]; rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3857 = 5179 := by
  calc
    Artifact.submissionArtifact.instructionPC 3857 =
        Artifact.submissionArtifact.instructionPC 3856 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3856 _ (by rfl)
    _ = 5179 := by rw [fixedPC3923]; rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3858 = 5182 := by
  calc
    Artifact.submissionArtifact.instructionPC 3858 =
        Artifact.submissionArtifact.instructionPC 3857 + (YulEvmCompiler.Instr.push 2 7200).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3857 _ (by rfl)
    _ = 5182 := by rw [fixedPC3924]; rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3859 = 5183 := by
  calc
    Artifact.submissionArtifact.instructionPC 3859 =
        Artifact.submissionArtifact.instructionPC 3858 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3858 _ (by rfl)
    _ = 5183 := by rw [fixedPC3925]; rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3860 = 5186 := by
  calc
    Artifact.submissionArtifact.instructionPC 3860 =
        Artifact.submissionArtifact.instructionPC 3859 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3859 _ (by rfl)
    _ = 5186 := by rw [fixedPC3926]; rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3861 = 5187 := by
  calc
    Artifact.submissionArtifact.instructionPC 3861 =
        Artifact.submissionArtifact.instructionPC 3860 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3860 _ (by rfl)
    _ = 5187 := by rw [fixedPC3927]; rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3862 = 5188 := by
  calc
    Artifact.submissionArtifact.instructionPC 3862 =
        Artifact.submissionArtifact.instructionPC 3861 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3861 _ (by rfl)
    _ = 5188 := by rw [fixedPC3928]; rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3863 = 5189 := by
  calc
    Artifact.submissionArtifact.instructionPC 3863 =
        Artifact.submissionArtifact.instructionPC 3862 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3862 _ (by rfl)
    _ = 5189 := by rw [fixedPC3929]; rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3864 = 5190 := by
  calc
    Artifact.submissionArtifact.instructionPC 3864 =
        Artifact.submissionArtifact.instructionPC 3863 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3863 _ (by rfl)
    _ = 5190 := by rw [fixedPC3930]; rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3865 = 5191 := by
  calc
    Artifact.submissionArtifact.instructionPC 3865 =
        Artifact.submissionArtifact.instructionPC 3864 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3864 _ (by rfl)
    _ = 5191 := by rw [fixedPC3931]; rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3866 = 5192 := by
  calc
    Artifact.submissionArtifact.instructionPC 3866 =
        Artifact.submissionArtifact.instructionPC 3865 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3865 _ (by rfl)
    _ = 5192 := by rw [fixedPC3932]; rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3867 = 5193 := by
  calc
    Artifact.submissionArtifact.instructionPC 3867 =
        Artifact.submissionArtifact.instructionPC 3866 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3866 _ (by rfl)
    _ = 5193 := by rw [fixedPC3933]; rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3868 = 5194 := by
  calc
    Artifact.submissionArtifact.instructionPC 3868 =
        Artifact.submissionArtifact.instructionPC 3867 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3867 _ (by rfl)
    _ = 5194 := by rw [fixedPC3934]; rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3869 = 5195 := by
  calc
    Artifact.submissionArtifact.instructionPC 3869 =
        Artifact.submissionArtifact.instructionPC 3868 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3868 _ (by rfl)
    _ = 5195 := by rw [fixedPC3935]; rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3870 = 5196 := by
  calc
    Artifact.submissionArtifact.instructionPC 3870 =
        Artifact.submissionArtifact.instructionPC 3869 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3869 _ (by rfl)
    _ = 5196 := by rw [fixedPC3936]; rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3871 = 5197 := by
  calc
    Artifact.submissionArtifact.instructionPC 3871 =
        Artifact.submissionArtifact.instructionPC 3870 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3870 _ (by rfl)
    _ = 5197 := by rw [fixedPC3937]; rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3872 = 5198 := by
  calc
    Artifact.submissionArtifact.instructionPC 3872 =
        Artifact.submissionArtifact.instructionPC 3871 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3871 _ (by rfl)
    _ = 5198 := by rw [fixedPC3938]; rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3873 = 5199 := by
  calc
    Artifact.submissionArtifact.instructionPC 3873 =
        Artifact.submissionArtifact.instructionPC 3872 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3872 _ (by rfl)
    _ = 5199 := by rw [fixedPC3939]; rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3874 = 5200 := by
  calc
    Artifact.submissionArtifact.instructionPC 3874 =
        Artifact.submissionArtifact.instructionPC 3873 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3873 _ (by rfl)
    _ = 5200 := by rw [fixedPC3940]; rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3875 = 5201 := by
  calc
    Artifact.submissionArtifact.instructionPC 3875 =
        Artifact.submissionArtifact.instructionPC 3874 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3874 _ (by rfl)
    _ = 5201 := by rw [fixedPC3941]; rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3876 = 5204 := by
  calc
    Artifact.submissionArtifact.instructionPC 3876 =
        Artifact.submissionArtifact.instructionPC 3875 + (YulEvmCompiler.Instr.push 2 7168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3875 _ (by rfl)
    _ = 5204 := by rw [fixedPC3942]; rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3877 = 5205 := by
  calc
    Artifact.submissionArtifact.instructionPC 3877 =
        Artifact.submissionArtifact.instructionPC 3876 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3876 _ (by rfl)
    _ = 5205 := by rw [fixedPC3943]; rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3878 = 5206 := by
  calc
    Artifact.submissionArtifact.instructionPC 3878 =
        Artifact.submissionArtifact.instructionPC 3877 + (YulEvmCompiler.Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3877 _ (by rfl)
    _ = 5206 := by rw [fixedPC3944]; rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3879 = 5209 := by
  calc
    Artifact.submissionArtifact.instructionPC 3879 =
        Artifact.submissionArtifact.instructionPC 3878 + (YulEvmCompiler.Instr.push 2 8224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3878 _ (by rfl)
    _ = 5209 := by rw [fixedPC3945]; rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3880 = 5210 := by
  calc
    Artifact.submissionArtifact.instructionPC 3880 =
        Artifact.submissionArtifact.instructionPC 3879 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3879 _ (by rfl)
    _ = 5210 := by rw [fixedPC3946]; rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3881 = 5211 := by
  calc
    Artifact.submissionArtifact.instructionPC 3881 =
        Artifact.submissionArtifact.instructionPC 3880 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3880 _ (by rfl)
    _ = 5211 := by rw [fixedPC3947]; rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3882 = 5244 := by
  calc
    Artifact.submissionArtifact.instructionPC 3882 =
        Artifact.submissionArtifact.instructionPC 3881 + (YulEvmCompiler.Instr.push 32 115792089237316195423570985008687907853269984665640564039457584007913129638848).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3881 _ (by rfl)
    _ = 5244 := by rw [fixedPC3948]; rfl

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3882 = 5244 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3883 = 5245 := by
  calc
    Artifact.submissionArtifact.instructionPC 3883 =
        Artifact.submissionArtifact.instructionPC 3882 + (YulEvmCompiler.Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3882 _ (by rfl)
    _ = 5245 := by rw [fixedPC3950]; rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3884 = 5248 := by
  calc
    Artifact.submissionArtifact.instructionPC 3884 =
        Artifact.submissionArtifact.instructionPC 3883 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3883 _ (by rfl)
    _ = 5248 := by rw [fixedPC3951]; rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3885 = 5249 := by
  calc
    Artifact.submissionArtifact.instructionPC 3885 =
        Artifact.submissionArtifact.instructionPC 3884 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3884 _ (by rfl)
    _ = 5249 := by rw [fixedPC3952]; rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3886 = 5252 := by
  calc
    Artifact.submissionArtifact.instructionPC 3886 =
        Artifact.submissionArtifact.instructionPC 3885 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3885 _ (by rfl)
    _ = 5252 := by rw [fixedPC3953]; rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3887 = 5253 := by
  calc
    Artifact.submissionArtifact.instructionPC 3887 =
        Artifact.submissionArtifact.instructionPC 3886 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3886 _ (by rfl)
    _ = 5253 := by rw [fixedPC3954]; rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3888 = 5254 := by
  calc
    Artifact.submissionArtifact.instructionPC 3888 =
        Artifact.submissionArtifact.instructionPC 3887 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3887 _ (by rfl)
    _ = 5254 := by rw [fixedPC3955]; rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3889 = 5255 := by
  calc
    Artifact.submissionArtifact.instructionPC 3889 =
        Artifact.submissionArtifact.instructionPC 3888 + (YulEvmCompiler.Instr.op .MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3888 _ (by rfl)
    _ = 5255 := by rw [fixedPC3956]; rfl

@[simp] theorem fixedPC3958 : Artifact.submissionArtifact.instructionPC 3890 = 5256 := by
  calc
    Artifact.submissionArtifact.instructionPC 3890 =
        Artifact.submissionArtifact.instructionPC 3889 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3889 _ (by rfl)
    _ = 5256 := by rw [fixedPC3957]; rfl

@[simp] theorem fixedJump5224 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5256 = true := by
  simpa only [Artifact.instructionPC, fixedPC3958] using Artifact.isValidJumpDest_index 3890 (by rfl)

@[simp] theorem fixedPC3959 : Artifact.submissionArtifact.instructionPC 3891 = 5257 := by
  calc
    Artifact.submissionArtifact.instructionPC 3891 =
        Artifact.submissionArtifact.instructionPC 3890 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3890 _ (by rfl)
    _ = 5257 := by rw [fixedPC3958]; rfl

@[simp] theorem fixedPC3960 : Artifact.submissionArtifact.instructionPC 3892 = 5258 := by
  calc
    Artifact.submissionArtifact.instructionPC 3892 =
        Artifact.submissionArtifact.instructionPC 3891 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3891 _ (by rfl)
    _ = 5258 := by rw [fixedPC3959]; rfl

@[simp] theorem fixedPC3961 : Artifact.submissionArtifact.instructionPC 3893 = 5259 := by
  calc
    Artifact.submissionArtifact.instructionPC 3893 =
        Artifact.submissionArtifact.instructionPC 3892 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3892 _ (by rfl)
    _ = 5259 := by rw [fixedPC3960]; rfl

@[simp] theorem fixedPC3962 : Artifact.submissionArtifact.instructionPC 3894 = 5261 := by
  calc
    Artifact.submissionArtifact.instructionPC 3894 =
        Artifact.submissionArtifact.instructionPC 3893 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3893 _ (by rfl)
    _ = 5261 := by rw [fixedPC3961]; rfl

@[simp] theorem fixedPC3963 : Artifact.submissionArtifact.instructionPC 3895 = 5262 := by
  calc
    Artifact.submissionArtifact.instructionPC 3895 =
        Artifact.submissionArtifact.instructionPC 3894 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3894 _ (by rfl)
    _ = 5262 := by rw [fixedPC3962]; rfl

@[simp] theorem fixedPC3964 : Artifact.submissionArtifact.instructionPC 3896 = 5264 := by
  calc
    Artifact.submissionArtifact.instructionPC 3896 =
        Artifact.submissionArtifact.instructionPC 3895 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3895 _ (by rfl)
    _ = 5264 := by rw [fixedPC3963]; rfl

@[simp] theorem fixedPC3965 : Artifact.submissionArtifact.instructionPC 3897 = 5265 := by
  calc
    Artifact.submissionArtifact.instructionPC 3897 =
        Artifact.submissionArtifact.instructionPC 3896 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3896 _ (by rfl)
    _ = 5265 := by rw [fixedPC3964]; rfl

@[simp] theorem fixedPC3966 : Artifact.submissionArtifact.instructionPC 3898 = 5267 := by
  calc
    Artifact.submissionArtifact.instructionPC 3898 =
        Artifact.submissionArtifact.instructionPC 3897 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3897 _ (by rfl)
    _ = 5267 := by rw [fixedPC3965]; rfl

@[simp] theorem fixedPC3967 : Artifact.submissionArtifact.instructionPC 3899 = 5268 := by
  calc
    Artifact.submissionArtifact.instructionPC 3899 =
        Artifact.submissionArtifact.instructionPC 3898 + (YulEvmCompiler.Instr.op (.Dup ⟨3, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3898 _ (by rfl)
    _ = 5268 := by rw [fixedPC3966]; rfl

@[simp] theorem fixedPC3968 : Artifact.submissionArtifact.instructionPC 3900 = 5269 := by
  calc
    Artifact.submissionArtifact.instructionPC 3900 =
        Artifact.submissionArtifact.instructionPC 3899 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3899 _ (by rfl)
    _ = 5269 := by rw [fixedPC3967]; rfl

@[simp] theorem fixedPC3969 : Artifact.submissionArtifact.instructionPC 3901 = 5270 := by
  calc
    Artifact.submissionArtifact.instructionPC 3901 =
        Artifact.submissionArtifact.instructionPC 3900 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3900 _ (by rfl)
    _ = 5270 := by rw [fixedPC3968]; rfl

@[simp] theorem fixedPC3970 : Artifact.submissionArtifact.instructionPC 3902 = 5272 := by
  calc
    Artifact.submissionArtifact.instructionPC 3902 =
        Artifact.submissionArtifact.instructionPC 3901 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3901 _ (by rfl)
    _ = 5272 := by rw [fixedPC3969]; rfl

@[simp] theorem fixedPC3971 : Artifact.submissionArtifact.instructionPC 3903 = 5273 := by
  calc
    Artifact.submissionArtifact.instructionPC 3903 =
        Artifact.submissionArtifact.instructionPC 3902 + (YulEvmCompiler.Instr.op .XOR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3902 _ (by rfl)
    _ = 5273 := by rw [fixedPC3970]; rfl

@[simp] theorem fixedPC3972 : Artifact.submissionArtifact.instructionPC 3904 = 5274 := by
  calc
    Artifact.submissionArtifact.instructionPC 3904 =
        Artifact.submissionArtifact.instructionPC 3903 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3903 _ (by rfl)
    _ = 5274 := by rw [fixedPC3971]; rfl

@[simp] theorem fixedPC3973 : Artifact.submissionArtifact.instructionPC 3905 = 5275 := by
  calc
    Artifact.submissionArtifact.instructionPC 3905 =
        Artifact.submissionArtifact.instructionPC 3904 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3904 _ (by rfl)
    _ = 5275 := by rw [fixedPC3972]; rfl

@[simp] theorem fixedPC3974 : Artifact.submissionArtifact.instructionPC 3906 = 5277 := by
  calc
    Artifact.submissionArtifact.instructionPC 3906 =
        Artifact.submissionArtifact.instructionPC 3905 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3905 _ (by rfl)
    _ = 5277 := by rw [fixedPC3973]; rfl

@[simp] theorem fixedPC3975 : Artifact.submissionArtifact.instructionPC 3907 = 5278 := by
  calc
    Artifact.submissionArtifact.instructionPC 3907 =
        Artifact.submissionArtifact.instructionPC 3906 + (YulEvmCompiler.Instr.op .XOR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3906 _ (by rfl)
    _ = 5278 := by rw [fixedPC3974]; rfl

@[simp] theorem fixedPC3976 : Artifact.submissionArtifact.instructionPC 3908 = 5279 := by
  calc
    Artifact.submissionArtifact.instructionPC 3908 =
        Artifact.submissionArtifact.instructionPC 3907 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3907 _ (by rfl)
    _ = 5279 := by rw [fixedPC3975]; rfl

@[simp] theorem fixedPC3977 : Artifact.submissionArtifact.instructionPC 3909 = 5282 := by
  calc
    Artifact.submissionArtifact.instructionPC 3909 =
        Artifact.submissionArtifact.instructionPC 3908 + (YulEvmCompiler.Instr.push 2 5304).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3908 _ (by rfl)
    _ = 5282 := by rw [fixedPC3976]; rfl

@[simp] theorem fixedPC3978 : Artifact.submissionArtifact.instructionPC 3910 = 5283 := by
  calc
    Artifact.submissionArtifact.instructionPC 3910 =
        Artifact.submissionArtifact.instructionPC 3909 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3909 _ (by rfl)
    _ = 5283 := by rw [fixedPC3977]; rfl

@[simp] theorem fixedPC3979 : Artifact.submissionArtifact.instructionPC 3911 = 5284 := by
  calc
    Artifact.submissionArtifact.instructionPC 3911 =
        Artifact.submissionArtifact.instructionPC 3910 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3910 _ (by rfl)
    _ = 5284 := by rw [fixedPC3978]; rfl

@[simp] theorem fixedPC3980 : Artifact.submissionArtifact.instructionPC 3912 = 5286 := by
  calc
    Artifact.submissionArtifact.instructionPC 3912 =
        Artifact.submissionArtifact.instructionPC 3911 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3911 _ (by rfl)
    _ = 5286 := by rw [fixedPC3979]; rfl

@[simp] theorem fixedPC3981 : Artifact.submissionArtifact.instructionPC 3913 = 5287 := by
  calc
    Artifact.submissionArtifact.instructionPC 3913 =
        Artifact.submissionArtifact.instructionPC 3912 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3912 _ (by rfl)
    _ = 5287 := by rw [fixedPC3980]; rfl

@[simp] theorem fixedPC3982 : Artifact.submissionArtifact.instructionPC 3914 = 5288 := by
  calc
    Artifact.submissionArtifact.instructionPC 3914 =
        Artifact.submissionArtifact.instructionPC 3913 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3913 _ (by rfl)
    _ = 5288 := by rw [fixedPC3981]; rfl

@[simp] theorem fixedPC3983 : Artifact.submissionArtifact.instructionPC 3915 = 5289 := by
  calc
    Artifact.submissionArtifact.instructionPC 3915 =
        Artifact.submissionArtifact.instructionPC 3914 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3914 _ (by rfl)
    _ = 5289 := by rw [fixedPC3982]; rfl

@[simp] theorem fixedPC3984 : Artifact.submissionArtifact.instructionPC 3916 = 5290 := by
  calc
    Artifact.submissionArtifact.instructionPC 3916 =
        Artifact.submissionArtifact.instructionPC 3915 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3915 _ (by rfl)
    _ = 5290 := by rw [fixedPC3983]; rfl

@[simp] theorem fixedPC3985 : Artifact.submissionArtifact.instructionPC 3917 = 5293 := by
  calc
    Artifact.submissionArtifact.instructionPC 3917 =
        Artifact.submissionArtifact.instructionPC 3916 + (YulEvmCompiler.Instr.push 2 1186).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3916 _ (by rfl)
    _ = 5293 := by rw [fixedPC3984]; rfl

@[simp] theorem fixedPC3986 : Artifact.submissionArtifact.instructionPC 3918 = 5294 := by
  calc
    Artifact.submissionArtifact.instructionPC 3918 =
        Artifact.submissionArtifact.instructionPC 3917 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3917 _ (by rfl)
    _ = 5294 := by rw [fixedPC3985]; rfl

@[simp] theorem fixedPC3987 : Artifact.submissionArtifact.instructionPC 3919 = 5295 := by
  calc
    Artifact.submissionArtifact.instructionPC 3919 =
        Artifact.submissionArtifact.instructionPC 3918 + (YulEvmCompiler.Instr.op (.Dup ⟨3, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3918 _ (by rfl)
    _ = 5295 := by rw [fixedPC3986]; rfl

@[simp] theorem fixedPC3988 : Artifact.submissionArtifact.instructionPC 3920 = 5297 := by
  calc
    Artifact.submissionArtifact.instructionPC 3920 =
        Artifact.submissionArtifact.instructionPC 3919 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3919 _ (by rfl)
    _ = 5297 := by rw [fixedPC3987]; rfl

@[simp] theorem fixedPC3989 : Artifact.submissionArtifact.instructionPC 3921 = 5298 := by
  calc
    Artifact.submissionArtifact.instructionPC 3921 =
        Artifact.submissionArtifact.instructionPC 3920 + (YulEvmCompiler.Instr.op (.Dup ⟨6, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3920 _ (by rfl)
    _ = 5298 := by rw [fixedPC3988]; rfl

@[simp] theorem fixedPC3990 : Artifact.submissionArtifact.instructionPC 3922 = 5299 := by
  calc
    Artifact.submissionArtifact.instructionPC 3922 =
        Artifact.submissionArtifact.instructionPC 3921 + (YulEvmCompiler.Instr.op (.Dup ⟨8, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3921 _ (by rfl)
    _ = 5299 := by rw [fixedPC3989]; rfl

@[simp] theorem fixedPC3991 : Artifact.submissionArtifact.instructionPC 3923 = 5300 := by
  calc
    Artifact.submissionArtifact.instructionPC 3923 =
        Artifact.submissionArtifact.instructionPC 3922 + (YulEvmCompiler.Instr.op (.Dup ⟨10, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3922 _ (by rfl)
    _ = 5300 := by rw [fixedPC3990]; rfl

@[simp] theorem fixedPC3992 : Artifact.submissionArtifact.instructionPC 3924 = 5303 := by
  calc
    Artifact.submissionArtifact.instructionPC 3924 =
        Artifact.submissionArtifact.instructionPC 3923 + (YulEvmCompiler.Instr.push 2 4888).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3923 _ (by rfl)
    _ = 5303 := by rw [fixedPC3991]; rfl

@[simp] theorem fixedPC3993 : Artifact.submissionArtifact.instructionPC 3925 = 5304 := by
  calc
    Artifact.submissionArtifact.instructionPC 3925 =
        Artifact.submissionArtifact.instructionPC 3924 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3924 _ (by rfl)
    _ = 5304 := by rw [fixedPC3992]; rfl

@[simp] theorem fixedJump5272 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5304 = true := by
  simpa only [Artifact.instructionPC, fixedPC3993] using Artifact.isValidJumpDest_index 3925 (by rfl)

@[simp] theorem fixedPC3994 : Artifact.submissionArtifact.instructionPC 3926 = 5305 := by
  calc
    Artifact.submissionArtifact.instructionPC 3926 =
        Artifact.submissionArtifact.instructionPC 3925 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3925 _ (by rfl)
    _ = 5305 := by rw [fixedPC3993]; rfl

@[simp] theorem fixedPC3995 : Artifact.submissionArtifact.instructionPC 3927 = 5306 := by
  calc
    Artifact.submissionArtifact.instructionPC 3927 =
        Artifact.submissionArtifact.instructionPC 3926 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3926 _ (by rfl)
    _ = 5306 := by rw [fixedPC3994]; rfl

@[simp] theorem fixedPC3996 : Artifact.submissionArtifact.instructionPC 3928 = 5307 := by
  calc
    Artifact.submissionArtifact.instructionPC 3928 =
        Artifact.submissionArtifact.instructionPC 3927 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3927 _ (by rfl)
    _ = 5307 := by rw [fixedPC3995]; rfl

@[simp] theorem fixedPC3997 : Artifact.submissionArtifact.instructionPC 3929 = 5308 := by
  calc
    Artifact.submissionArtifact.instructionPC 3929 =
        Artifact.submissionArtifact.instructionPC 3928 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3928 _ (by rfl)
    _ = 5308 := by rw [fixedPC3996]; rfl

@[simp] theorem fixedPC3998 : Artifact.submissionArtifact.instructionPC 3930 = 5311 := by
  calc
    Artifact.submissionArtifact.instructionPC 3930 =
        Artifact.submissionArtifact.instructionPC 3929 + (YulEvmCompiler.Instr.push 2 1233).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3929 _ (by rfl)
    _ = 5311 := by rw [fixedPC3997]; rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3931 = 5312 := by
  calc
    Artifact.submissionArtifact.instructionPC 3931 =
        Artifact.submissionArtifact.instructionPC 3930 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3930 _ (by rfl)
    _ = 5312 := by rw [fixedPC3998]; rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5312 = true := by
  simpa only [Artifact.instructionPC, fixedPC3999] using Artifact.isValidJumpDest_index 3931 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3932 = 5313 := by
  calc
    Artifact.submissionArtifact.instructionPC 3932 =
        Artifact.submissionArtifact.instructionPC 3931 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3931 _ (by rfl)
    _ = 5313 := by rw [fixedPC3999]; rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3933 = 5316 := by
  calc
    Artifact.submissionArtifact.instructionPC 3933 =
        Artifact.submissionArtifact.instructionPC 3932 + (YulEvmCompiler.Instr.push 2 8352).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3932 _ (by rfl)
    _ = 5316 := by rw [fixedPC4000]; rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3934 = 5317 := by
  calc
    Artifact.submissionArtifact.instructionPC 3934 =
        Artifact.submissionArtifact.instructionPC 3933 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3933 _ (by rfl)
    _ = 5317 := by rw [fixedPC4001]; rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3935 = 5319 := by
  calc
    Artifact.submissionArtifact.instructionPC 3935 =
        Artifact.submissionArtifact.instructionPC 3934 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3934 _ (by rfl)
    _ = 5319 := by rw [fixedPC4002]; rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3936 = 5320 := by
  calc
    Artifact.submissionArtifact.instructionPC 3936 =
        Artifact.submissionArtifact.instructionPC 3935 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3935 _ (by rfl)
    _ = 5320 := by rw [fixedPC4003]; rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3937 = 5321 := by
  calc
    Artifact.submissionArtifact.instructionPC 3937 =
        Artifact.submissionArtifact.instructionPC 3936 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3936 _ (by rfl)
    _ = 5321 := by rw [fixedPC4004]; rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3938 = 5322 := by
  calc
    Artifact.submissionArtifact.instructionPC 3938 =
        Artifact.submissionArtifact.instructionPC 3937 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3937 _ (by rfl)
    _ = 5322 := by rw [fixedPC4005]; rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3939 = 5323 := by
  calc
    Artifact.submissionArtifact.instructionPC 3939 =
        Artifact.submissionArtifact.instructionPC 3938 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3938 _ (by rfl)
    _ = 5323 := by rw [fixedPC4006]; rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3940 = 5324 := by
  calc
    Artifact.submissionArtifact.instructionPC 3940 =
        Artifact.submissionArtifact.instructionPC 3939 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3939 _ (by rfl)
    _ = 5324 := by rw [fixedPC4007]; rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3941 = 5325 := by
  calc
    Artifact.submissionArtifact.instructionPC 3941 =
        Artifact.submissionArtifact.instructionPC 3940 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3940 _ (by rfl)
    _ = 5325 := by rw [fixedPC4008]; rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3942 = 5328 := by
  calc
    Artifact.submissionArtifact.instructionPC 3942 =
        Artifact.submissionArtifact.instructionPC 3941 + (YulEvmCompiler.Instr.push 2 7264).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3941 _ (by rfl)
    _ = 5328 := by rw [fixedPC4009]; rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3943 = 5329 := by
  calc
    Artifact.submissionArtifact.instructionPC 3943 =
        Artifact.submissionArtifact.instructionPC 3942 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3942 _ (by rfl)
    _ = 5329 := by rw [fixedPC4010]; rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3944 = 5332 := by
  calc
    Artifact.submissionArtifact.instructionPC 3944 =
        Artifact.submissionArtifact.instructionPC 3943 + (YulEvmCompiler.Instr.push 2 5136).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3943 _ (by rfl)
    _ = 5332 := by rw [fixedPC4011]; rfl

end Challenge.Modexp.Submission.Proofs.Fast
