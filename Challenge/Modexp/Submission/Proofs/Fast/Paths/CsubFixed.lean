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
  [opAt 3662 .JUMPDEST,
   pushAt 3663 2 9344,
   opAt 3664 .MLOAD,
   pushAt 3665 2 256,
   opAt 3666 .EQ,
   pushAt 3667 2 4870,
   opAt 3668 .JUMPI,
   pushAt 3669 2 9344,
   opAt 3670 .MLOAD,
   pushAt 3671 1 128,
   opAt 3672 .EQ,
   pushAt 3673 2 4664,
   opAt 3674 .JUMPI,
   pushAt 3675 2 9440,
   opAt 3676 .MLOAD,
   pushAt 3677 2 9408,
   opAt 3678 .MLOAD,
   opAt 3679 (.Dup ⟨0, by decide⟩),
   pushAt 3680 2 7168,
   opAt 3681 .ADD,
   pushAt 3682 2 8256,
   opAt 3683 .POP,
   opAt 3684 (.Swap ⟨0, by decide⟩),
   pushAt 3685 0 0,
   opAt 3686 (.Swap ⟨2, by decide⟩),
   pushAt 3687 2 1997,
   opAt 3688 .JUMP]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3662 .JUMPDEST,
   pushAt 3663 2 9344,
   opAt 3664 .MLOAD,
   pushAt 3665 2 256,
   opAt 3666 .EQ,
   pushAt 3667 2 4870,
   opAt 3668 .JUMPI,
   opAt 3689 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3662 .JUMPDEST,
   pushAt 3663 2 9344,
   opAt 3664 .MLOAD,
   pushAt 3665 2 256,
   opAt 3666 .EQ,
   pushAt 3667 2 4870,
   opAt 3668 .JUMPI,
   pushAt 3669 2 9344,
   opAt 3670 .MLOAD,
   pushAt 3671 1 128,
   opAt 3672 .EQ,
   pushAt 3673 2 4664,
   opAt 3674 .JUMPI,
   opAt 3559 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3690 2 8480,
   opAt 3691 .MLOAD,
   pushAt 3692 1 224,
   opAt 3693 .MLOAD,
   opAt 3694 (.Dup ⟨1, by decide⟩),
   opAt 3695 (.Dup ⟨1, by decide⟩),
   opAt 3696 .GT,
   opAt 3697 (.Swap ⟨1, by decide⟩),
   opAt 3698 .SUB,
   pushAt 3699 2 7392,
   opAt 3700 .MSTORE]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3701 2 8448,
   opAt 3702 .MLOAD,
   pushAt 3703 1 192,
   opAt 3704 .MLOAD,
   opAt 3705 (.Dup ⟨1, by decide⟩),
   opAt 3706 (.Dup ⟨1, by decide⟩),
   opAt 3707 .GT,
   opAt 3708 (.Swap ⟨1, by decide⟩),
   opAt 3709 .SUB,
   opAt 3710 (.Dup ⟨2, by decide⟩),
   opAt 3711 (.Dup ⟨1, by decide⟩),
   opAt 3712 .SUB,
   opAt 3713 (.Swap ⟨2, by decide⟩),
   opAt 3714 .GT,
   opAt 3715 .OR,
   opAt 3716 (.Swap ⟨0, by decide⟩),
   pushAt 3717 2 7360,
   opAt 3718 .MSTORE]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3719 2 8416,
   opAt 3720 .MLOAD,
   pushAt 3721 1 160,
   opAt 3722 .MLOAD,
   opAt 3723 (.Dup ⟨1, by decide⟩),
   opAt 3724 (.Dup ⟨1, by decide⟩),
   opAt 3725 .GT,
   opAt 3726 (.Swap ⟨1, by decide⟩),
   opAt 3727 .SUB,
   opAt 3728 (.Dup ⟨2, by decide⟩),
   opAt 3729 (.Dup ⟨1, by decide⟩),
   opAt 3730 .SUB,
   opAt 3731 (.Swap ⟨2, by decide⟩),
   opAt 3732 .GT,
   opAt 3733 .OR,
   opAt 3734 (.Swap ⟨0, by decide⟩),
   pushAt 3735 2 7328,
   opAt 3736 .MSTORE]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3737 2 8384,
   opAt 3738 .MLOAD,
   pushAt 3739 1 128,
   opAt 3740 .MLOAD,
   opAt 3741 (.Dup ⟨1, by decide⟩),
   opAt 3742 (.Dup ⟨1, by decide⟩),
   opAt 3743 .GT,
   opAt 3744 (.Swap ⟨1, by decide⟩),
   opAt 3745 .SUB,
   opAt 3746 (.Dup ⟨2, by decide⟩),
   opAt 3747 (.Dup ⟨1, by decide⟩),
   opAt 3748 .SUB,
   opAt 3749 (.Swap ⟨2, by decide⟩),
   opAt 3750 .GT,
   opAt 3751 .OR,
   opAt 3752 (.Swap ⟨0, by decide⟩),
   pushAt 3753 2 7296,
   opAt 3754 .MSTORE]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 3755 2 8352,
   opAt 3756 .MLOAD,
   pushAt 3757 1 96,
   opAt 3758 .MLOAD,
   opAt 3759 (.Dup ⟨1, by decide⟩),
   opAt 3760 (.Dup ⟨1, by decide⟩),
   opAt 3761 .GT,
   opAt 3762 (.Swap ⟨1, by decide⟩),
   opAt 3763 .SUB,
   opAt 3764 (.Dup ⟨2, by decide⟩),
   opAt 3765 (.Dup ⟨1, by decide⟩),
   opAt 3766 .SUB,
   opAt 3767 (.Swap ⟨2, by decide⟩),
   opAt 3768 .GT,
   opAt 3769 .OR,
   opAt 3770 (.Swap ⟨0, by decide⟩),
   pushAt 3771 2 7264,
   opAt 3772 .MSTORE]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3773 .JUMPDEST,
   pushAt 3774 2 8320,
   opAt 3775 .MLOAD,
   pushAt 3776 1 64,
   opAt 3777 .MLOAD,
   opAt 3778 (.Dup ⟨1, by decide⟩),
   opAt 3779 (.Dup ⟨1, by decide⟩),
   opAt 3780 .GT,
   opAt 3781 (.Swap ⟨1, by decide⟩),
   opAt 3782 .SUB,
   opAt 3783 (.Dup ⟨2, by decide⟩),
   opAt 3784 (.Dup ⟨1, by decide⟩),
   opAt 3785 .SUB,
   opAt 3786 (.Swap ⟨2, by decide⟩),
   opAt 3787 .GT,
   opAt 3788 .OR,
   opAt 3789 (.Swap ⟨0, by decide⟩),
   pushAt 3790 2 7232,
   opAt 3791 .MSTORE]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3792 2 8288,
   opAt 3793 .MLOAD,
   pushAt 3794 1 32,
   opAt 3795 .MLOAD,
   opAt 3796 (.Dup ⟨1, by decide⟩),
   opAt 3797 (.Dup ⟨1, by decide⟩),
   opAt 3798 .GT,
   opAt 3799 (.Swap ⟨1, by decide⟩),
   opAt 3800 .SUB,
   opAt 3801 (.Dup ⟨2, by decide⟩),
   opAt 3802 (.Dup ⟨1, by decide⟩),
   opAt 3803 .SUB,
   opAt 3804 (.Swap ⟨2, by decide⟩),
   opAt 3805 .GT,
   opAt 3806 .OR,
   opAt 3807 (.Swap ⟨0, by decide⟩),
   pushAt 3808 2 7200,
   opAt 3809 .MSTORE]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3810 2 8256,
   opAt 3811 .MLOAD,
   pushAt 3812 0 0,
   opAt 3813 .MLOAD,
   opAt 3814 (.Dup ⟨1, by decide⟩),
   opAt 3815 (.Dup ⟨1, by decide⟩),
   opAt 3816 .GT,
   opAt 3817 (.Swap ⟨1, by decide⟩),
   opAt 3818 .SUB,
   opAt 3819 (.Dup ⟨2, by decide⟩),
   opAt 3820 (.Dup ⟨1, by decide⟩),
   opAt 3821 .SUB,
   opAt 3822 (.Swap ⟨2, by decide⟩),
   opAt 3823 .GT,
   opAt 3824 .OR,
   opAt 3825 (.Swap ⟨0, by decide⟩),
   pushAt 3826 2 7168,
   opAt 3827 .MSTORE]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3828 .ISZERO,
   pushAt 3829 2 8224,
   opAt 3830 .MLOAD,
   opAt 3831 .OR,
   pushAt 3832 2 1087,
   opAt 3833 .NOT,
   pushAt 3834 2 5073,
   opAt 3835 .JUMP,
   opAt 3843 .JUMPDEST,
   opAt 3844 .MUL,
   pushAt 3845 2 8256,
   opAt 3846 .ADD,
   pushAt 3847 2 9344,
   opAt 3848 .MLOAD,
   opAt 3849 (.Swap ⟨1, by decide⟩),
   opAt 3850 .MCOPY,
   opAt 3851 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3560 2 8352,
   opAt 3561 .MLOAD,
   pushAt 3562 1 96,
   opAt 3563 .MLOAD,
   opAt 3564 (.Dup ⟨1, by decide⟩),
   opAt 3565 (.Dup ⟨1, by decide⟩),
   opAt 3566 .GT,
   opAt 3567 (.Swap ⟨1, by decide⟩),
   opAt 3568 .SUB,
   pushAt 3569 2 7264,
   opAt 3570 .MSTORE,
   pushAt 3571 2 4979,
   opAt 3572 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3773 .JUMPDEST,
   pushAt 3774 2 8320,
   opAt 3775 .MLOAD,
   pushAt 3776 1 64,
   opAt 3777 .MLOAD,
   opAt 3778 (.Dup ⟨1, by decide⟩),
   opAt 3779 (.Dup ⟨1, by decide⟩),
   opAt 3780 .GT,
   opAt 3781 (.Swap ⟨1, by decide⟩),
   opAt 3782 .SUB,
   opAt 3783 (.Dup ⟨2, by decide⟩),
   opAt 3784 (.Dup ⟨1, by decide⟩),
   opAt 3785 .SUB,
   opAt 3786 (.Swap ⟨2, by decide⟩),
   opAt 3787 .GT,
   opAt 3788 .OR,
   opAt 3789 (.Swap ⟨0, by decide⟩),
   pushAt 3790 2 7232,
   opAt 3791 .MSTORE]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3792 2 8288,
   opAt 3793 .MLOAD,
   pushAt 3794 1 32,
   opAt 3795 .MLOAD,
   opAt 3796 (.Dup ⟨1, by decide⟩),
   opAt 3797 (.Dup ⟨1, by decide⟩),
   opAt 3798 .GT,
   opAt 3799 (.Swap ⟨1, by decide⟩),
   opAt 3800 .SUB,
   opAt 3801 (.Dup ⟨2, by decide⟩),
   opAt 3802 (.Dup ⟨1, by decide⟩),
   opAt 3803 .SUB,
   opAt 3804 (.Swap ⟨2, by decide⟩),
   opAt 3805 .GT,
   opAt 3806 .OR,
   opAt 3807 (.Swap ⟨0, by decide⟩),
   pushAt 3808 2 7200,
   opAt 3809 .MSTORE]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3810 2 8256,
   opAt 3811 .MLOAD,
   pushAt 3812 0 0,
   opAt 3813 .MLOAD,
   opAt 3814 (.Dup ⟨1, by decide⟩),
   opAt 3815 (.Dup ⟨1, by decide⟩),
   opAt 3816 .GT,
   opAt 3817 (.Swap ⟨1, by decide⟩),
   opAt 3818 .SUB,
   opAt 3819 (.Dup ⟨2, by decide⟩),
   opAt 3820 (.Dup ⟨1, by decide⟩),
   opAt 3821 .SUB,
   opAt 3822 (.Swap ⟨2, by decide⟩),
   opAt 3823 .GT,
   opAt 3824 .OR,
   opAt 3825 (.Swap ⟨0, by decide⟩),
   pushAt 3826 2 7168,
   opAt 3827 .MSTORE]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3828 .ISZERO,
   pushAt 3829 2 8224,
   opAt 3830 .MLOAD,
   opAt 3831 .OR,
   pushAt 3832 2 1087,
   opAt 3833 .NOT,
   pushAt 3834 2 5073,
   opAt 3835 .JUMP,
   opAt 3843 .JUMPDEST,
   opAt 3844 .MUL,
   pushAt 3845 2 8256,
   opAt 3846 .ADD,
   pushAt 3847 2 9344,
   opAt 3848 .MLOAD,
   opAt 3849 (.Swap ⟨1, by decide⟩),
   opAt 3850 .MCOPY,
   opAt 3851 .JUMP]

@[simp] theorem fixedPC1618 : Artifact.submissionArtifact.instructionPC 1480 = 1993 := by rfl

@[simp] theorem fixedPC1619 : Artifact.submissionArtifact.instructionPC 1481 = 1996 := by
  calc
    Artifact.submissionArtifact.instructionPC 1481 =
        Artifact.submissionArtifact.instructionPC 1480 + (YulEvmCompiler.Instr.push 2 4642).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1480 _ (by rfl)
    _ = 1996 := by rw [fixedPC1618]; rfl

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3662 = 4822 := by rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4822 = true := by
  simpa only [Artifact.instructionPC, fixedPC3777] using Artifact.isValidJumpDest_index 3662 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3663 = 4823 := by
  calc
    Artifact.submissionArtifact.instructionPC 3663 =
        Artifact.submissionArtifact.instructionPC 3662 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3662 _ (by rfl)
    _ = 4823 := by rw [fixedPC3777]; rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3664 = 4826 := by
  calc
    Artifact.submissionArtifact.instructionPC 3664 =
        Artifact.submissionArtifact.instructionPC 3663 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3663 _ (by rfl)
    _ = 4826 := by rw [fixedPC3778]; rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3665 = 4827 := by
  calc
    Artifact.submissionArtifact.instructionPC 3665 =
        Artifact.submissionArtifact.instructionPC 3664 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3664 _ (by rfl)
    _ = 4827 := by rw [fixedPC3779]; rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3666 = 4830 := by
  calc
    Artifact.submissionArtifact.instructionPC 3666 =
        Artifact.submissionArtifact.instructionPC 3665 + (YulEvmCompiler.Instr.push 2 256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3665 _ (by rfl)
    _ = 4830 := by rw [fixedPC3780]; rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3667 = 4831 := by
  calc
    Artifact.submissionArtifact.instructionPC 3667 =
        Artifact.submissionArtifact.instructionPC 3666 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3666 _ (by rfl)
    _ = 4831 := by rw [fixedPC3781]; rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3668 = 4834 := by
  calc
    Artifact.submissionArtifact.instructionPC 3668 =
        Artifact.submissionArtifact.instructionPC 3667 + (YulEvmCompiler.Instr.push 2 4870).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3667 _ (by rfl)
    _ = 4834 := by rw [fixedPC3782]; rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3669 = 4835 := by
  calc
    Artifact.submissionArtifact.instructionPC 3669 =
        Artifact.submissionArtifact.instructionPC 3668 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3668 _ (by rfl)
    _ = 4835 := by rw [fixedPC3783]; rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3670 = 4838 := by
  calc
    Artifact.submissionArtifact.instructionPC 3670 =
        Artifact.submissionArtifact.instructionPC 3669 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3669 _ (by rfl)
    _ = 4838 := by rw [fixedPC3784]; rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3671 = 4839 := by
  calc
    Artifact.submissionArtifact.instructionPC 3671 =
        Artifact.submissionArtifact.instructionPC 3670 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3670 _ (by rfl)
    _ = 4839 := by rw [fixedPC3785]; rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3672 = 4841 := by
  calc
    Artifact.submissionArtifact.instructionPC 3672 =
        Artifact.submissionArtifact.instructionPC 3671 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3671 _ (by rfl)
    _ = 4841 := by rw [fixedPC3786]; rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3673 = 4842 := by
  calc
    Artifact.submissionArtifact.instructionPC 3673 =
        Artifact.submissionArtifact.instructionPC 3672 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3672 _ (by rfl)
    _ = 4842 := by rw [fixedPC3787]; rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3674 = 4845 := by
  calc
    Artifact.submissionArtifact.instructionPC 3674 =
        Artifact.submissionArtifact.instructionPC 3673 + (YulEvmCompiler.Instr.push 2 4664).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3673 _ (by rfl)
    _ = 4845 := by rw [fixedPC3788]; rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3675 = 4846 := by
  calc
    Artifact.submissionArtifact.instructionPC 3675 =
        Artifact.submissionArtifact.instructionPC 3674 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3674 _ (by rfl)
    _ = 4846 := by rw [fixedPC3789]; rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3676 = 4849 := by
  calc
    Artifact.submissionArtifact.instructionPC 3676 =
        Artifact.submissionArtifact.instructionPC 3675 + (YulEvmCompiler.Instr.push 2 9440).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3675 _ (by rfl)
    _ = 4849 := by rw [fixedPC3790]; rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3677 = 4850 := by
  calc
    Artifact.submissionArtifact.instructionPC 3677 =
        Artifact.submissionArtifact.instructionPC 3676 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3676 _ (by rfl)
    _ = 4850 := by rw [fixedPC3791]; rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3678 = 4853 := by
  calc
    Artifact.submissionArtifact.instructionPC 3678 =
        Artifact.submissionArtifact.instructionPC 3677 + (YulEvmCompiler.Instr.push 2 9408).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3677 _ (by rfl)
    _ = 4853 := by rw [fixedPC3792]; rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3679 = 4854 := by
  calc
    Artifact.submissionArtifact.instructionPC 3679 =
        Artifact.submissionArtifact.instructionPC 3678 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3678 _ (by rfl)
    _ = 4854 := by rw [fixedPC3793]; rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3680 = 4855 := by
  calc
    Artifact.submissionArtifact.instructionPC 3680 =
        Artifact.submissionArtifact.instructionPC 3679 + (YulEvmCompiler.Instr.op (.Dup ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3679 _ (by rfl)
    _ = 4855 := by rw [fixedPC3794]; rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3681 = 4858 := by
  calc
    Artifact.submissionArtifact.instructionPC 3681 =
        Artifact.submissionArtifact.instructionPC 3680 + (YulEvmCompiler.Instr.push 2 7168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3680 _ (by rfl)
    _ = 4858 := by rw [fixedPC3795]; rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3682 = 4859 := by
  calc
    Artifact.submissionArtifact.instructionPC 3682 =
        Artifact.submissionArtifact.instructionPC 3681 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3681 _ (by rfl)
    _ = 4859 := by rw [fixedPC3796]; rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3683 = 4862 := by
  calc
    Artifact.submissionArtifact.instructionPC 3683 =
        Artifact.submissionArtifact.instructionPC 3682 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3682 _ (by rfl)
    _ = 4862 := by rw [fixedPC3797]; rfl

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3684 = 4863 := by
  calc
    Artifact.submissionArtifact.instructionPC 3684 =
        Artifact.submissionArtifact.instructionPC 3683 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3683 _ (by rfl)
    _ = 4863 := by rw [fixedPC3798]; rfl

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3685 = 4864 := by
  calc
    Artifact.submissionArtifact.instructionPC 3685 =
        Artifact.submissionArtifact.instructionPC 3684 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3684 _ (by rfl)
    _ = 4864 := by rw [fixedPC3799]; rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3686 = 4865 := by
  calc
    Artifact.submissionArtifact.instructionPC 3686 =
        Artifact.submissionArtifact.instructionPC 3685 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3685 _ (by rfl)
    _ = 4865 := by rw [fixedPC3800]; rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3687 = 4866 := by
  calc
    Artifact.submissionArtifact.instructionPC 3687 =
        Artifact.submissionArtifact.instructionPC 3686 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3686 _ (by rfl)
    _ = 4866 := by rw [fixedPC3801]; rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3688 = 4869 := by
  calc
    Artifact.submissionArtifact.instructionPC 3688 =
        Artifact.submissionArtifact.instructionPC 3687 + (YulEvmCompiler.Instr.push 2 1997).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3687 _ (by rfl)
    _ = 4869 := by rw [fixedPC3802]; rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3689 = 4870 := by
  calc
    Artifact.submissionArtifact.instructionPC 3689 =
        Artifact.submissionArtifact.instructionPC 3688 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3688 _ (by rfl)
    _ = 4870 := by rw [fixedPC3803]; rfl

@[simp] theorem fixedJump5023 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4870 = true := by
  simpa only [Artifact.instructionPC, fixedPC3804] using Artifact.isValidJumpDest_index 3689 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3690 = 4871 := by
  calc
    Artifact.submissionArtifact.instructionPC 3690 =
        Artifact.submissionArtifact.instructionPC 3689 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3689 _ (by rfl)
    _ = 4871 := by rw [fixedPC3804]; rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3691 = 4874 := by
  calc
    Artifact.submissionArtifact.instructionPC 3691 =
        Artifact.submissionArtifact.instructionPC 3690 + (YulEvmCompiler.Instr.push 2 8480).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3690 _ (by rfl)
    _ = 4874 := by rw [fixedPC3805]; rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3692 = 4875 := by
  calc
    Artifact.submissionArtifact.instructionPC 3692 =
        Artifact.submissionArtifact.instructionPC 3691 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3691 _ (by rfl)
    _ = 4875 := by rw [fixedPC3806]; rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3693 = 4877 := by
  calc
    Artifact.submissionArtifact.instructionPC 3693 =
        Artifact.submissionArtifact.instructionPC 3692 + (YulEvmCompiler.Instr.push 1 224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3692 _ (by rfl)
    _ = 4877 := by rw [fixedPC3807]; rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3694 = 4878 := by
  calc
    Artifact.submissionArtifact.instructionPC 3694 =
        Artifact.submissionArtifact.instructionPC 3693 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3693 _ (by rfl)
    _ = 4878 := by rw [fixedPC3808]; rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3695 = 4879 := by
  calc
    Artifact.submissionArtifact.instructionPC 3695 =
        Artifact.submissionArtifact.instructionPC 3694 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3694 _ (by rfl)
    _ = 4879 := by rw [fixedPC3809]; rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3696 = 4880 := by
  calc
    Artifact.submissionArtifact.instructionPC 3696 =
        Artifact.submissionArtifact.instructionPC 3695 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3695 _ (by rfl)
    _ = 4880 := by rw [fixedPC3810]; rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3697 = 4881 := by
  calc
    Artifact.submissionArtifact.instructionPC 3697 =
        Artifact.submissionArtifact.instructionPC 3696 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3696 _ (by rfl)
    _ = 4881 := by rw [fixedPC3811]; rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3698 = 4882 := by
  calc
    Artifact.submissionArtifact.instructionPC 3698 =
        Artifact.submissionArtifact.instructionPC 3697 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3697 _ (by rfl)
    _ = 4882 := by rw [fixedPC3812]; rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3699 = 4883 := by
  calc
    Artifact.submissionArtifact.instructionPC 3699 =
        Artifact.submissionArtifact.instructionPC 3698 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3698 _ (by rfl)
    _ = 4883 := by rw [fixedPC3813]; rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3700 = 4886 := by
  calc
    Artifact.submissionArtifact.instructionPC 3700 =
        Artifact.submissionArtifact.instructionPC 3699 + (YulEvmCompiler.Instr.push 2 7392).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3699 _ (by rfl)
    _ = 4886 := by rw [fixedPC3814]; rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3701 = 4887 := by
  calc
    Artifact.submissionArtifact.instructionPC 3701 =
        Artifact.submissionArtifact.instructionPC 3700 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3700 _ (by rfl)
    _ = 4887 := by rw [fixedPC3815]; rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3702 = 4890 := by
  calc
    Artifact.submissionArtifact.instructionPC 3702 =
        Artifact.submissionArtifact.instructionPC 3701 + (YulEvmCompiler.Instr.push 2 8448).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3701 _ (by rfl)
    _ = 4890 := by rw [fixedPC3816]; rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3703 = 4891 := by
  calc
    Artifact.submissionArtifact.instructionPC 3703 =
        Artifact.submissionArtifact.instructionPC 3702 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3702 _ (by rfl)
    _ = 4891 := by rw [fixedPC3817]; rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3704 = 4893 := by
  calc
    Artifact.submissionArtifact.instructionPC 3704 =
        Artifact.submissionArtifact.instructionPC 3703 + (YulEvmCompiler.Instr.push 1 192).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3703 _ (by rfl)
    _ = 4893 := by rw [fixedPC3818]; rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3705 = 4894 := by
  calc
    Artifact.submissionArtifact.instructionPC 3705 =
        Artifact.submissionArtifact.instructionPC 3704 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3704 _ (by rfl)
    _ = 4894 := by rw [fixedPC3819]; rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3706 = 4895 := by
  calc
    Artifact.submissionArtifact.instructionPC 3706 =
        Artifact.submissionArtifact.instructionPC 3705 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3705 _ (by rfl)
    _ = 4895 := by rw [fixedPC3820]; rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3707 = 4896 := by
  calc
    Artifact.submissionArtifact.instructionPC 3707 =
        Artifact.submissionArtifact.instructionPC 3706 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3706 _ (by rfl)
    _ = 4896 := by rw [fixedPC3821]; rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3708 = 4897 := by
  calc
    Artifact.submissionArtifact.instructionPC 3708 =
        Artifact.submissionArtifact.instructionPC 3707 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3707 _ (by rfl)
    _ = 4897 := by rw [fixedPC3822]; rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3709 = 4898 := by
  calc
    Artifact.submissionArtifact.instructionPC 3709 =
        Artifact.submissionArtifact.instructionPC 3708 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3708 _ (by rfl)
    _ = 4898 := by rw [fixedPC3823]; rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3710 = 4899 := by
  calc
    Artifact.submissionArtifact.instructionPC 3710 =
        Artifact.submissionArtifact.instructionPC 3709 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3709 _ (by rfl)
    _ = 4899 := by rw [fixedPC3824]; rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3711 = 4900 := by
  calc
    Artifact.submissionArtifact.instructionPC 3711 =
        Artifact.submissionArtifact.instructionPC 3710 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3710 _ (by rfl)
    _ = 4900 := by rw [fixedPC3825]; rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3712 = 4901 := by
  calc
    Artifact.submissionArtifact.instructionPC 3712 =
        Artifact.submissionArtifact.instructionPC 3711 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3711 _ (by rfl)
    _ = 4901 := by rw [fixedPC3826]; rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3713 = 4902 := by
  calc
    Artifact.submissionArtifact.instructionPC 3713 =
        Artifact.submissionArtifact.instructionPC 3712 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3712 _ (by rfl)
    _ = 4902 := by rw [fixedPC3827]; rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3714 = 4903 := by
  calc
    Artifact.submissionArtifact.instructionPC 3714 =
        Artifact.submissionArtifact.instructionPC 3713 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3713 _ (by rfl)
    _ = 4903 := by rw [fixedPC3828]; rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3715 = 4904 := by
  calc
    Artifact.submissionArtifact.instructionPC 3715 =
        Artifact.submissionArtifact.instructionPC 3714 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3714 _ (by rfl)
    _ = 4904 := by rw [fixedPC3829]; rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3716 = 4905 := by
  calc
    Artifact.submissionArtifact.instructionPC 3716 =
        Artifact.submissionArtifact.instructionPC 3715 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3715 _ (by rfl)
    _ = 4905 := by rw [fixedPC3830]; rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3717 = 4906 := by
  calc
    Artifact.submissionArtifact.instructionPC 3717 =
        Artifact.submissionArtifact.instructionPC 3716 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3716 _ (by rfl)
    _ = 4906 := by rw [fixedPC3831]; rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3718 = 4909 := by
  calc
    Artifact.submissionArtifact.instructionPC 3718 =
        Artifact.submissionArtifact.instructionPC 3717 + (YulEvmCompiler.Instr.push 2 7360).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3717 _ (by rfl)
    _ = 4909 := by rw [fixedPC3832]; rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3719 = 4910 := by
  calc
    Artifact.submissionArtifact.instructionPC 3719 =
        Artifact.submissionArtifact.instructionPC 3718 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3718 _ (by rfl)
    _ = 4910 := by rw [fixedPC3833]; rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3720 = 4913 := by
  calc
    Artifact.submissionArtifact.instructionPC 3720 =
        Artifact.submissionArtifact.instructionPC 3719 + (YulEvmCompiler.Instr.push 2 8416).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3719 _ (by rfl)
    _ = 4913 := by rw [fixedPC3834]; rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3721 = 4914 := by
  calc
    Artifact.submissionArtifact.instructionPC 3721 =
        Artifact.submissionArtifact.instructionPC 3720 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3720 _ (by rfl)
    _ = 4914 := by rw [fixedPC3835]; rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3722 = 4916 := by
  calc
    Artifact.submissionArtifact.instructionPC 3722 =
        Artifact.submissionArtifact.instructionPC 3721 + (YulEvmCompiler.Instr.push 1 160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3721 _ (by rfl)
    _ = 4916 := by rw [fixedPC3836]; rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3723 = 4917 := by
  calc
    Artifact.submissionArtifact.instructionPC 3723 =
        Artifact.submissionArtifact.instructionPC 3722 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3722 _ (by rfl)
    _ = 4917 := by rw [fixedPC3837]; rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3724 = 4918 := by
  calc
    Artifact.submissionArtifact.instructionPC 3724 =
        Artifact.submissionArtifact.instructionPC 3723 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3723 _ (by rfl)
    _ = 4918 := by rw [fixedPC3838]; rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3725 = 4919 := by
  calc
    Artifact.submissionArtifact.instructionPC 3725 =
        Artifact.submissionArtifact.instructionPC 3724 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3724 _ (by rfl)
    _ = 4919 := by rw [fixedPC3839]; rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3726 = 4920 := by
  calc
    Artifact.submissionArtifact.instructionPC 3726 =
        Artifact.submissionArtifact.instructionPC 3725 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3725 _ (by rfl)
    _ = 4920 := by rw [fixedPC3840]; rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3727 = 4921 := by
  calc
    Artifact.submissionArtifact.instructionPC 3727 =
        Artifact.submissionArtifact.instructionPC 3726 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3726 _ (by rfl)
    _ = 4921 := by rw [fixedPC3841]; rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3728 = 4922 := by
  calc
    Artifact.submissionArtifact.instructionPC 3728 =
        Artifact.submissionArtifact.instructionPC 3727 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3727 _ (by rfl)
    _ = 4922 := by rw [fixedPC3842]; rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3729 = 4923 := by
  calc
    Artifact.submissionArtifact.instructionPC 3729 =
        Artifact.submissionArtifact.instructionPC 3728 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3728 _ (by rfl)
    _ = 4923 := by rw [fixedPC3843]; rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3730 = 4924 := by
  calc
    Artifact.submissionArtifact.instructionPC 3730 =
        Artifact.submissionArtifact.instructionPC 3729 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3729 _ (by rfl)
    _ = 4924 := by rw [fixedPC3844]; rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3731 = 4925 := by
  calc
    Artifact.submissionArtifact.instructionPC 3731 =
        Artifact.submissionArtifact.instructionPC 3730 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3730 _ (by rfl)
    _ = 4925 := by rw [fixedPC3845]; rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3732 = 4926 := by
  calc
    Artifact.submissionArtifact.instructionPC 3732 =
        Artifact.submissionArtifact.instructionPC 3731 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3731 _ (by rfl)
    _ = 4926 := by rw [fixedPC3846]; rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3733 = 4927 := by
  calc
    Artifact.submissionArtifact.instructionPC 3733 =
        Artifact.submissionArtifact.instructionPC 3732 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3732 _ (by rfl)
    _ = 4927 := by rw [fixedPC3847]; rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3734 = 4928 := by
  calc
    Artifact.submissionArtifact.instructionPC 3734 =
        Artifact.submissionArtifact.instructionPC 3733 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3733 _ (by rfl)
    _ = 4928 := by rw [fixedPC3848]; rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3735 = 4929 := by
  calc
    Artifact.submissionArtifact.instructionPC 3735 =
        Artifact.submissionArtifact.instructionPC 3734 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3734 _ (by rfl)
    _ = 4929 := by rw [fixedPC3849]; rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3736 = 4932 := by
  calc
    Artifact.submissionArtifact.instructionPC 3736 =
        Artifact.submissionArtifact.instructionPC 3735 + (YulEvmCompiler.Instr.push 2 7328).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3735 _ (by rfl)
    _ = 4932 := by rw [fixedPC3850]; rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3737 = 4933 := by
  calc
    Artifact.submissionArtifact.instructionPC 3737 =
        Artifact.submissionArtifact.instructionPC 3736 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3736 _ (by rfl)
    _ = 4933 := by rw [fixedPC3851]; rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3738 = 4936 := by
  calc
    Artifact.submissionArtifact.instructionPC 3738 =
        Artifact.submissionArtifact.instructionPC 3737 + (YulEvmCompiler.Instr.push 2 8384).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3737 _ (by rfl)
    _ = 4936 := by rw [fixedPC3852]; rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3739 = 4937 := by
  calc
    Artifact.submissionArtifact.instructionPC 3739 =
        Artifact.submissionArtifact.instructionPC 3738 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3738 _ (by rfl)
    _ = 4937 := by rw [fixedPC3853]; rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3740 = 4939 := by
  calc
    Artifact.submissionArtifact.instructionPC 3740 =
        Artifact.submissionArtifact.instructionPC 3739 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3739 _ (by rfl)
    _ = 4939 := by rw [fixedPC3854]; rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3741 = 4940 := by
  calc
    Artifact.submissionArtifact.instructionPC 3741 =
        Artifact.submissionArtifact.instructionPC 3740 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3740 _ (by rfl)
    _ = 4940 := by rw [fixedPC3855]; rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3742 = 4941 := by
  calc
    Artifact.submissionArtifact.instructionPC 3742 =
        Artifact.submissionArtifact.instructionPC 3741 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3741 _ (by rfl)
    _ = 4941 := by rw [fixedPC3856]; rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3743 = 4942 := by
  calc
    Artifact.submissionArtifact.instructionPC 3743 =
        Artifact.submissionArtifact.instructionPC 3742 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3742 _ (by rfl)
    _ = 4942 := by rw [fixedPC3857]; rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3744 = 4943 := by
  calc
    Artifact.submissionArtifact.instructionPC 3744 =
        Artifact.submissionArtifact.instructionPC 3743 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3743 _ (by rfl)
    _ = 4943 := by rw [fixedPC3858]; rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3745 = 4944 := by
  calc
    Artifact.submissionArtifact.instructionPC 3745 =
        Artifact.submissionArtifact.instructionPC 3744 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3744 _ (by rfl)
    _ = 4944 := by rw [fixedPC3859]; rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3746 = 4945 := by
  calc
    Artifact.submissionArtifact.instructionPC 3746 =
        Artifact.submissionArtifact.instructionPC 3745 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3745 _ (by rfl)
    _ = 4945 := by rw [fixedPC3860]; rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3747 = 4946 := by
  calc
    Artifact.submissionArtifact.instructionPC 3747 =
        Artifact.submissionArtifact.instructionPC 3746 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3746 _ (by rfl)
    _ = 4946 := by rw [fixedPC3861]; rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3748 = 4947 := by
  calc
    Artifact.submissionArtifact.instructionPC 3748 =
        Artifact.submissionArtifact.instructionPC 3747 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3747 _ (by rfl)
    _ = 4947 := by rw [fixedPC3862]; rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3749 = 4948 := by
  calc
    Artifact.submissionArtifact.instructionPC 3749 =
        Artifact.submissionArtifact.instructionPC 3748 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3748 _ (by rfl)
    _ = 4948 := by rw [fixedPC3863]; rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3750 = 4949 := by
  calc
    Artifact.submissionArtifact.instructionPC 3750 =
        Artifact.submissionArtifact.instructionPC 3749 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3749 _ (by rfl)
    _ = 4949 := by rw [fixedPC3864]; rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3751 = 4950 := by
  calc
    Artifact.submissionArtifact.instructionPC 3751 =
        Artifact.submissionArtifact.instructionPC 3750 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3750 _ (by rfl)
    _ = 4950 := by rw [fixedPC3865]; rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3752 = 4951 := by
  calc
    Artifact.submissionArtifact.instructionPC 3752 =
        Artifact.submissionArtifact.instructionPC 3751 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3751 _ (by rfl)
    _ = 4951 := by rw [fixedPC3866]; rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3753 = 4952 := by
  calc
    Artifact.submissionArtifact.instructionPC 3753 =
        Artifact.submissionArtifact.instructionPC 3752 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3752 _ (by rfl)
    _ = 4952 := by rw [fixedPC3867]; rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3754 = 4955 := by
  calc
    Artifact.submissionArtifact.instructionPC 3754 =
        Artifact.submissionArtifact.instructionPC 3753 + (YulEvmCompiler.Instr.push 2 7296).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3753 _ (by rfl)
    _ = 4955 := by rw [fixedPC3868]; rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3755 = 4956 := by
  calc
    Artifact.submissionArtifact.instructionPC 3755 =
        Artifact.submissionArtifact.instructionPC 3754 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3754 _ (by rfl)
    _ = 4956 := by rw [fixedPC3869]; rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3756 = 4959 := by
  calc
    Artifact.submissionArtifact.instructionPC 3756 =
        Artifact.submissionArtifact.instructionPC 3755 + (YulEvmCompiler.Instr.push 2 8352).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3755 _ (by rfl)
    _ = 4959 := by rw [fixedPC3871]; rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3757 = 4960 := by
  calc
    Artifact.submissionArtifact.instructionPC 3757 =
        Artifact.submissionArtifact.instructionPC 3756 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3756 _ (by rfl)
    _ = 4960 := by rw [fixedPC3872]; rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3758 = 4962 := by
  calc
    Artifact.submissionArtifact.instructionPC 3758 =
        Artifact.submissionArtifact.instructionPC 3757 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3757 _ (by rfl)
    _ = 4962 := by rw [fixedPC3873]; rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3759 = 4963 := by
  calc
    Artifact.submissionArtifact.instructionPC 3759 =
        Artifact.submissionArtifact.instructionPC 3758 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3758 _ (by rfl)
    _ = 4963 := by rw [fixedPC3874]; rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3760 = 4964 := by
  calc
    Artifact.submissionArtifact.instructionPC 3760 =
        Artifact.submissionArtifact.instructionPC 3759 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3759 _ (by rfl)
    _ = 4964 := by rw [fixedPC3875]; rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3761 = 4965 := by
  calc
    Artifact.submissionArtifact.instructionPC 3761 =
        Artifact.submissionArtifact.instructionPC 3760 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3760 _ (by rfl)
    _ = 4965 := by rw [fixedPC3876]; rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3762 = 4966 := by
  calc
    Artifact.submissionArtifact.instructionPC 3762 =
        Artifact.submissionArtifact.instructionPC 3761 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3761 _ (by rfl)
    _ = 4966 := by rw [fixedPC3877]; rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3763 = 4967 := by
  calc
    Artifact.submissionArtifact.instructionPC 3763 =
        Artifact.submissionArtifact.instructionPC 3762 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3762 _ (by rfl)
    _ = 4967 := by rw [fixedPC3878]; rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3764 = 4968 := by
  calc
    Artifact.submissionArtifact.instructionPC 3764 =
        Artifact.submissionArtifact.instructionPC 3763 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3763 _ (by rfl)
    _ = 4968 := by rw [fixedPC3879]; rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3765 = 4969 := by
  calc
    Artifact.submissionArtifact.instructionPC 3765 =
        Artifact.submissionArtifact.instructionPC 3764 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3764 _ (by rfl)
    _ = 4969 := by rw [fixedPC3880]; rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3766 = 4970 := by
  calc
    Artifact.submissionArtifact.instructionPC 3766 =
        Artifact.submissionArtifact.instructionPC 3765 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3765 _ (by rfl)
    _ = 4970 := by rw [fixedPC3881]; rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3767 = 4971 := by
  calc
    Artifact.submissionArtifact.instructionPC 3767 =
        Artifact.submissionArtifact.instructionPC 3766 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3766 _ (by rfl)
    _ = 4971 := by rw [fixedPC3882]; rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3768 = 4972 := by
  calc
    Artifact.submissionArtifact.instructionPC 3768 =
        Artifact.submissionArtifact.instructionPC 3767 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3767 _ (by rfl)
    _ = 4972 := by rw [fixedPC3883]; rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3769 = 4973 := by
  calc
    Artifact.submissionArtifact.instructionPC 3769 =
        Artifact.submissionArtifact.instructionPC 3768 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3768 _ (by rfl)
    _ = 4973 := by rw [fixedPC3884]; rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3770 = 4974 := by
  calc
    Artifact.submissionArtifact.instructionPC 3770 =
        Artifact.submissionArtifact.instructionPC 3769 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3769 _ (by rfl)
    _ = 4974 := by rw [fixedPC3885]; rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3771 = 4975 := by
  calc
    Artifact.submissionArtifact.instructionPC 3771 =
        Artifact.submissionArtifact.instructionPC 3770 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3770 _ (by rfl)
    _ = 4975 := by rw [fixedPC3886]; rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3772 = 4978 := by
  calc
    Artifact.submissionArtifact.instructionPC 3772 =
        Artifact.submissionArtifact.instructionPC 3771 + (YulEvmCompiler.Instr.push 2 7264).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3771 _ (by rfl)
    _ = 4978 := by rw [fixedPC3887]; rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3773 = 4979 := by
  calc
    Artifact.submissionArtifact.instructionPC 3773 =
        Artifact.submissionArtifact.instructionPC 3772 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3772 _ (by rfl)
    _ = 4979 := by rw [fixedPC3888]; rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4979 = true := by
  simpa only [Artifact.instructionPC, fixedPC3889] using Artifact.isValidJumpDest_index 3773 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3774 = 4980 := by
  calc
    Artifact.submissionArtifact.instructionPC 3774 =
        Artifact.submissionArtifact.instructionPC 3773 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3773 _ (by rfl)
    _ = 4980 := by rw [fixedPC3889]; rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3775 = 4983 := by
  calc
    Artifact.submissionArtifact.instructionPC 3775 =
        Artifact.submissionArtifact.instructionPC 3774 + (YulEvmCompiler.Instr.push 2 8320).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3774 _ (by rfl)
    _ = 4983 := by rw [fixedPC3890]; rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3776 = 4984 := by
  calc
    Artifact.submissionArtifact.instructionPC 3776 =
        Artifact.submissionArtifact.instructionPC 3775 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3775 _ (by rfl)
    _ = 4984 := by rw [fixedPC3891]; rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3777 = 4986 := by
  calc
    Artifact.submissionArtifact.instructionPC 3777 =
        Artifact.submissionArtifact.instructionPC 3776 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3776 _ (by rfl)
    _ = 4986 := by rw [fixedPC3892]; rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3778 = 4987 := by
  calc
    Artifact.submissionArtifact.instructionPC 3778 =
        Artifact.submissionArtifact.instructionPC 3777 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3777 _ (by rfl)
    _ = 4987 := by rw [fixedPC3893]; rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3779 = 4988 := by
  calc
    Artifact.submissionArtifact.instructionPC 3779 =
        Artifact.submissionArtifact.instructionPC 3778 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3778 _ (by rfl)
    _ = 4988 := by rw [fixedPC3894]; rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3780 = 4989 := by
  calc
    Artifact.submissionArtifact.instructionPC 3780 =
        Artifact.submissionArtifact.instructionPC 3779 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3779 _ (by rfl)
    _ = 4989 := by rw [fixedPC3895]; rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3781 = 4990 := by
  calc
    Artifact.submissionArtifact.instructionPC 3781 =
        Artifact.submissionArtifact.instructionPC 3780 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3780 _ (by rfl)
    _ = 4990 := by rw [fixedPC3896]; rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3782 = 4991 := by
  calc
    Artifact.submissionArtifact.instructionPC 3782 =
        Artifact.submissionArtifact.instructionPC 3781 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3781 _ (by rfl)
    _ = 4991 := by rw [fixedPC3897]; rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3783 = 4992 := by
  calc
    Artifact.submissionArtifact.instructionPC 3783 =
        Artifact.submissionArtifact.instructionPC 3782 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3782 _ (by rfl)
    _ = 4992 := by rw [fixedPC3898]; rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3784 = 4993 := by
  calc
    Artifact.submissionArtifact.instructionPC 3784 =
        Artifact.submissionArtifact.instructionPC 3783 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3783 _ (by rfl)
    _ = 4993 := by rw [fixedPC3899]; rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3785 = 4994 := by
  calc
    Artifact.submissionArtifact.instructionPC 3785 =
        Artifact.submissionArtifact.instructionPC 3784 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3784 _ (by rfl)
    _ = 4994 := by rw [fixedPC3900]; rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3786 = 4995 := by
  calc
    Artifact.submissionArtifact.instructionPC 3786 =
        Artifact.submissionArtifact.instructionPC 3785 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3785 _ (by rfl)
    _ = 4995 := by rw [fixedPC3901]; rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3787 = 4996 := by
  calc
    Artifact.submissionArtifact.instructionPC 3787 =
        Artifact.submissionArtifact.instructionPC 3786 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3786 _ (by rfl)
    _ = 4996 := by rw [fixedPC3902]; rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3788 = 4997 := by
  calc
    Artifact.submissionArtifact.instructionPC 3788 =
        Artifact.submissionArtifact.instructionPC 3787 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3787 _ (by rfl)
    _ = 4997 := by rw [fixedPC3903]; rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3789 = 4998 := by
  calc
    Artifact.submissionArtifact.instructionPC 3789 =
        Artifact.submissionArtifact.instructionPC 3788 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3788 _ (by rfl)
    _ = 4998 := by rw [fixedPC3904]; rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3790 = 4999 := by
  calc
    Artifact.submissionArtifact.instructionPC 3790 =
        Artifact.submissionArtifact.instructionPC 3789 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3789 _ (by rfl)
    _ = 4999 := by rw [fixedPC3905]; rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3791 = 5002 := by
  calc
    Artifact.submissionArtifact.instructionPC 3791 =
        Artifact.submissionArtifact.instructionPC 3790 + (YulEvmCompiler.Instr.push 2 7232).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3790 _ (by rfl)
    _ = 5002 := by rw [fixedPC3906]; rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3792 = 5003 := by
  calc
    Artifact.submissionArtifact.instructionPC 3792 =
        Artifact.submissionArtifact.instructionPC 3791 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3791 _ (by rfl)
    _ = 5003 := by rw [fixedPC3907]; rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3793 = 5006 := by
  calc
    Artifact.submissionArtifact.instructionPC 3793 =
        Artifact.submissionArtifact.instructionPC 3792 + (YulEvmCompiler.Instr.push 2 8288).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3792 _ (by rfl)
    _ = 5006 := by rw [fixedPC3908]; rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3794 = 5007 := by
  calc
    Artifact.submissionArtifact.instructionPC 3794 =
        Artifact.submissionArtifact.instructionPC 3793 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3793 _ (by rfl)
    _ = 5007 := by rw [fixedPC3909]; rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3795 = 5009 := by
  calc
    Artifact.submissionArtifact.instructionPC 3795 =
        Artifact.submissionArtifact.instructionPC 3794 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3794 _ (by rfl)
    _ = 5009 := by rw [fixedPC3910]; rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3796 = 5010 := by
  calc
    Artifact.submissionArtifact.instructionPC 3796 =
        Artifact.submissionArtifact.instructionPC 3795 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3795 _ (by rfl)
    _ = 5010 := by rw [fixedPC3911]; rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3797 = 5011 := by
  calc
    Artifact.submissionArtifact.instructionPC 3797 =
        Artifact.submissionArtifact.instructionPC 3796 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3796 _ (by rfl)
    _ = 5011 := by rw [fixedPC3912]; rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3798 = 5012 := by
  calc
    Artifact.submissionArtifact.instructionPC 3798 =
        Artifact.submissionArtifact.instructionPC 3797 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3797 _ (by rfl)
    _ = 5012 := by rw [fixedPC3913]; rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3799 = 5013 := by
  calc
    Artifact.submissionArtifact.instructionPC 3799 =
        Artifact.submissionArtifact.instructionPC 3798 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3798 _ (by rfl)
    _ = 5013 := by rw [fixedPC3914]; rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3800 = 5014 := by
  calc
    Artifact.submissionArtifact.instructionPC 3800 =
        Artifact.submissionArtifact.instructionPC 3799 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3799 _ (by rfl)
    _ = 5014 := by rw [fixedPC3915]; rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3801 = 5015 := by
  calc
    Artifact.submissionArtifact.instructionPC 3801 =
        Artifact.submissionArtifact.instructionPC 3800 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3800 _ (by rfl)
    _ = 5015 := by rw [fixedPC3916]; rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3802 = 5016 := by
  calc
    Artifact.submissionArtifact.instructionPC 3802 =
        Artifact.submissionArtifact.instructionPC 3801 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3801 _ (by rfl)
    _ = 5016 := by rw [fixedPC3917]; rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3803 = 5017 := by
  calc
    Artifact.submissionArtifact.instructionPC 3803 =
        Artifact.submissionArtifact.instructionPC 3802 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3802 _ (by rfl)
    _ = 5017 := by rw [fixedPC3918]; rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3804 = 5018 := by
  calc
    Artifact.submissionArtifact.instructionPC 3804 =
        Artifact.submissionArtifact.instructionPC 3803 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3803 _ (by rfl)
    _ = 5018 := by rw [fixedPC3919]; rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3805 = 5019 := by
  calc
    Artifact.submissionArtifact.instructionPC 3805 =
        Artifact.submissionArtifact.instructionPC 3804 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3804 _ (by rfl)
    _ = 5019 := by rw [fixedPC3920]; rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3806 = 5020 := by
  calc
    Artifact.submissionArtifact.instructionPC 3806 =
        Artifact.submissionArtifact.instructionPC 3805 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3805 _ (by rfl)
    _ = 5020 := by rw [fixedPC3921]; rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3807 = 5021 := by
  calc
    Artifact.submissionArtifact.instructionPC 3807 =
        Artifact.submissionArtifact.instructionPC 3806 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3806 _ (by rfl)
    _ = 5021 := by rw [fixedPC3922]; rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3808 = 5022 := by
  calc
    Artifact.submissionArtifact.instructionPC 3808 =
        Artifact.submissionArtifact.instructionPC 3807 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3807 _ (by rfl)
    _ = 5022 := by rw [fixedPC3923]; rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3809 = 5025 := by
  calc
    Artifact.submissionArtifact.instructionPC 3809 =
        Artifact.submissionArtifact.instructionPC 3808 + (YulEvmCompiler.Instr.push 2 7200).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3808 _ (by rfl)
    _ = 5025 := by rw [fixedPC3924]; rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3810 = 5026 := by
  calc
    Artifact.submissionArtifact.instructionPC 3810 =
        Artifact.submissionArtifact.instructionPC 3809 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3809 _ (by rfl)
    _ = 5026 := by rw [fixedPC3925]; rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3811 = 5029 := by
  calc
    Artifact.submissionArtifact.instructionPC 3811 =
        Artifact.submissionArtifact.instructionPC 3810 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3810 _ (by rfl)
    _ = 5029 := by rw [fixedPC3926]; rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3812 = 5030 := by
  calc
    Artifact.submissionArtifact.instructionPC 3812 =
        Artifact.submissionArtifact.instructionPC 3811 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3811 _ (by rfl)
    _ = 5030 := by rw [fixedPC3927]; rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3813 = 5031 := by
  calc
    Artifact.submissionArtifact.instructionPC 3813 =
        Artifact.submissionArtifact.instructionPC 3812 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3812 _ (by rfl)
    _ = 5031 := by rw [fixedPC3928]; rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3814 = 5032 := by
  calc
    Artifact.submissionArtifact.instructionPC 3814 =
        Artifact.submissionArtifact.instructionPC 3813 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3813 _ (by rfl)
    _ = 5032 := by rw [fixedPC3929]; rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3815 = 5033 := by
  calc
    Artifact.submissionArtifact.instructionPC 3815 =
        Artifact.submissionArtifact.instructionPC 3814 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3814 _ (by rfl)
    _ = 5033 := by rw [fixedPC3930]; rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3816 = 5034 := by
  calc
    Artifact.submissionArtifact.instructionPC 3816 =
        Artifact.submissionArtifact.instructionPC 3815 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3815 _ (by rfl)
    _ = 5034 := by rw [fixedPC3931]; rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3817 = 5035 := by
  calc
    Artifact.submissionArtifact.instructionPC 3817 =
        Artifact.submissionArtifact.instructionPC 3816 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3816 _ (by rfl)
    _ = 5035 := by rw [fixedPC3932]; rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3818 = 5036 := by
  calc
    Artifact.submissionArtifact.instructionPC 3818 =
        Artifact.submissionArtifact.instructionPC 3817 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3817 _ (by rfl)
    _ = 5036 := by rw [fixedPC3933]; rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3819 = 5037 := by
  calc
    Artifact.submissionArtifact.instructionPC 3819 =
        Artifact.submissionArtifact.instructionPC 3818 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3818 _ (by rfl)
    _ = 5037 := by rw [fixedPC3934]; rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3820 = 5038 := by
  calc
    Artifact.submissionArtifact.instructionPC 3820 =
        Artifact.submissionArtifact.instructionPC 3819 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3819 _ (by rfl)
    _ = 5038 := by rw [fixedPC3935]; rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3821 = 5039 := by
  calc
    Artifact.submissionArtifact.instructionPC 3821 =
        Artifact.submissionArtifact.instructionPC 3820 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3820 _ (by rfl)
    _ = 5039 := by rw [fixedPC3936]; rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3822 = 5040 := by
  calc
    Artifact.submissionArtifact.instructionPC 3822 =
        Artifact.submissionArtifact.instructionPC 3821 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3821 _ (by rfl)
    _ = 5040 := by rw [fixedPC3937]; rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3823 = 5041 := by
  calc
    Artifact.submissionArtifact.instructionPC 3823 =
        Artifact.submissionArtifact.instructionPC 3822 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3822 _ (by rfl)
    _ = 5041 := by rw [fixedPC3938]; rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3824 = 5042 := by
  calc
    Artifact.submissionArtifact.instructionPC 3824 =
        Artifact.submissionArtifact.instructionPC 3823 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3823 _ (by rfl)
    _ = 5042 := by rw [fixedPC3939]; rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3825 = 5043 := by
  calc
    Artifact.submissionArtifact.instructionPC 3825 =
        Artifact.submissionArtifact.instructionPC 3824 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3824 _ (by rfl)
    _ = 5043 := by rw [fixedPC3940]; rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3826 = 5044 := by
  calc
    Artifact.submissionArtifact.instructionPC 3826 =
        Artifact.submissionArtifact.instructionPC 3825 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3825 _ (by rfl)
    _ = 5044 := by rw [fixedPC3941]; rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3827 = 5047 := by
  calc
    Artifact.submissionArtifact.instructionPC 3827 =
        Artifact.submissionArtifact.instructionPC 3826 + (YulEvmCompiler.Instr.push 2 7168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3826 _ (by rfl)
    _ = 5047 := by rw [fixedPC3942]; rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3828 = 5048 := by
  calc
    Artifact.submissionArtifact.instructionPC 3828 =
        Artifact.submissionArtifact.instructionPC 3827 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3827 _ (by rfl)
    _ = 5048 := by rw [fixedPC3943]; rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3829 = 5049 := by
  calc
    Artifact.submissionArtifact.instructionPC 3829 =
        Artifact.submissionArtifact.instructionPC 3828 + (YulEvmCompiler.Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3828 _ (by rfl)
    _ = 5049 := by rw [fixedPC3944]; rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3830 = 5052 := by
  calc
    Artifact.submissionArtifact.instructionPC 3830 =
        Artifact.submissionArtifact.instructionPC 3829 + (YulEvmCompiler.Instr.push 2 8224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3829 _ (by rfl)
    _ = 5052 := by rw [fixedPC3945]; rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3831 = 5053 := by
  calc
    Artifact.submissionArtifact.instructionPC 3831 =
        Artifact.submissionArtifact.instructionPC 3830 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3830 _ (by rfl)
    _ = 5053 := by rw [fixedPC3946]; rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3832 = 5054 := by
  calc
    Artifact.submissionArtifact.instructionPC 3832 =
        Artifact.submissionArtifact.instructionPC 3831 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3831 _ (by rfl)
    _ = 5054 := by rw [fixedPC3947]; rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3844 = 5074 := by
  decide

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3844 = 5074 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3845 = 5075 := by
  calc
    Artifact.submissionArtifact.instructionPC 3845 =
        Artifact.submissionArtifact.instructionPC 3844 + (YulEvmCompiler.Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3844 _ (by rfl)
    _ = 5075 := by rw [fixedPC3950]; rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3846 = 5078 := by
  calc
    Artifact.submissionArtifact.instructionPC 3846 =
        Artifact.submissionArtifact.instructionPC 3845 + (YulEvmCompiler.Instr.push 2 8256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3845 _ (by rfl)
    _ = 5078 := by rw [fixedPC3951]; rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3847 = 5079 := by
  calc
    Artifact.submissionArtifact.instructionPC 3847 =
        Artifact.submissionArtifact.instructionPC 3846 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3846 _ (by rfl)
    _ = 5079 := by rw [fixedPC3952]; rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3848 = 5082 := by
  calc
    Artifact.submissionArtifact.instructionPC 3848 =
        Artifact.submissionArtifact.instructionPC 3847 + (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3847 _ (by rfl)
    _ = 5082 := by rw [fixedPC3953]; rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3849 = 5083 := by
  calc
    Artifact.submissionArtifact.instructionPC 3849 =
        Artifact.submissionArtifact.instructionPC 3848 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3848 _ (by rfl)
    _ = 5083 := by rw [fixedPC3954]; rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3850 = 5084 := by
  calc
    Artifact.submissionArtifact.instructionPC 3850 =
        Artifact.submissionArtifact.instructionPC 3849 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3849 _ (by rfl)
    _ = 5084 := by rw [fixedPC3955]; rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3851 = 5085 := by
  calc
    Artifact.submissionArtifact.instructionPC 3851 =
        Artifact.submissionArtifact.instructionPC 3850 + (YulEvmCompiler.Instr.op .MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3850 _ (by rfl)
    _ = 5085 := by rw [fixedPC3956]; rfl

@[simp] theorem fixedPC3958 : Artifact.submissionArtifact.instructionPC 3852 = 5086 := by
  calc
    Artifact.submissionArtifact.instructionPC 3852 =
        Artifact.submissionArtifact.instructionPC 3851 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3851 _ (by rfl)
    _ = 5086 := by rw [fixedPC3957]; rfl

@[simp] theorem fixedJump5224 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5086 = true := by
  simpa only [Artifact.instructionPC, fixedPC3958] using Artifact.isValidJumpDest_index 3852 (by rfl)

@[simp] theorem fixedPC3959 : Artifact.submissionArtifact.instructionPC 3853 = 5087 := by
  calc
    Artifact.submissionArtifact.instructionPC 3853 =
        Artifact.submissionArtifact.instructionPC 3852 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3852 _ (by rfl)
    _ = 5087 := by rw [fixedPC3958]; rfl

@[simp] theorem fixedPC3960 : Artifact.submissionArtifact.instructionPC 3854 = 5088 := by
  calc
    Artifact.submissionArtifact.instructionPC 3854 =
        Artifact.submissionArtifact.instructionPC 3853 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3853 _ (by rfl)
    _ = 5088 := by rw [fixedPC3959]; rfl

@[simp] theorem fixedPC3961 : Artifact.submissionArtifact.instructionPC 3855 = 5089 := by
  calc
    Artifact.submissionArtifact.instructionPC 3855 =
        Artifact.submissionArtifact.instructionPC 3854 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3854 _ (by rfl)
    _ = 5089 := by rw [fixedPC3960]; rfl

@[simp] theorem fixedPC3962 : Artifact.submissionArtifact.instructionPC 3856 = 5091 := by
  calc
    Artifact.submissionArtifact.instructionPC 3856 =
        Artifact.submissionArtifact.instructionPC 3855 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3855 _ (by rfl)
    _ = 5091 := by rw [fixedPC3961]; rfl

@[simp] theorem fixedPC3963 : Artifact.submissionArtifact.instructionPC 3857 = 5092 := by
  calc
    Artifact.submissionArtifact.instructionPC 3857 =
        Artifact.submissionArtifact.instructionPC 3856 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3856 _ (by rfl)
    _ = 5092 := by rw [fixedPC3962]; rfl

@[simp] theorem fixedPC3964 : Artifact.submissionArtifact.instructionPC 3858 = 5094 := by
  calc
    Artifact.submissionArtifact.instructionPC 3858 =
        Artifact.submissionArtifact.instructionPC 3857 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3857 _ (by rfl)
    _ = 5094 := by rw [fixedPC3963]; rfl

@[simp] theorem fixedPC3965 : Artifact.submissionArtifact.instructionPC 3859 = 5095 := by
  calc
    Artifact.submissionArtifact.instructionPC 3859 =
        Artifact.submissionArtifact.instructionPC 3858 + (YulEvmCompiler.Instr.op .CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3858 _ (by rfl)
    _ = 5095 := by rw [fixedPC3964]; rfl

@[simp] theorem fixedPC3966 : Artifact.submissionArtifact.instructionPC 3860 = 5097 := by
  calc
    Artifact.submissionArtifact.instructionPC 3860 =
        Artifact.submissionArtifact.instructionPC 3859 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3859 _ (by rfl)
    _ = 5097 := by rw [fixedPC3965]; rfl

@[simp] theorem fixedPC3967 : Artifact.submissionArtifact.instructionPC 3861 = 5098 := by
  calc
    Artifact.submissionArtifact.instructionPC 3861 =
        Artifact.submissionArtifact.instructionPC 3860 + (YulEvmCompiler.Instr.op (.Dup ⟨3, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3860 _ (by rfl)
    _ = 5098 := by rw [fixedPC3966]; rfl

@[simp] theorem fixedPC3968 : Artifact.submissionArtifact.instructionPC 3862 = 5099 := by
  calc
    Artifact.submissionArtifact.instructionPC 3862 =
        Artifact.submissionArtifact.instructionPC 3861 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3861 _ (by rfl)
    _ = 5099 := by rw [fixedPC3967]; rfl

@[simp] theorem fixedPC3969 : Artifact.submissionArtifact.instructionPC 3863 = 5100 := by
  calc
    Artifact.submissionArtifact.instructionPC 3863 =
        Artifact.submissionArtifact.instructionPC 3862 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3862 _ (by rfl)
    _ = 5100 := by rw [fixedPC3968]; rfl

@[simp] theorem fixedPC3970 : Artifact.submissionArtifact.instructionPC 3864 = 5102 := by
  calc
    Artifact.submissionArtifact.instructionPC 3864 =
        Artifact.submissionArtifact.instructionPC 3863 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3863 _ (by rfl)
    _ = 5102 := by rw [fixedPC3969]; rfl

@[simp] theorem fixedPC3971 : Artifact.submissionArtifact.instructionPC 3865 = 5103 := by
  calc
    Artifact.submissionArtifact.instructionPC 3865 =
        Artifact.submissionArtifact.instructionPC 3864 + (YulEvmCompiler.Instr.op .XOR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3864 _ (by rfl)
    _ = 5103 := by rw [fixedPC3970]; rfl

@[simp] theorem fixedPC3972 : Artifact.submissionArtifact.instructionPC 3866 = 5104 := by
  calc
    Artifact.submissionArtifact.instructionPC 3866 =
        Artifact.submissionArtifact.instructionPC 3865 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3865 _ (by rfl)
    _ = 5104 := by rw [fixedPC3971]; rfl

@[simp] theorem fixedPC3973 : Artifact.submissionArtifact.instructionPC 3867 = 5105 := by
  calc
    Artifact.submissionArtifact.instructionPC 3867 =
        Artifact.submissionArtifact.instructionPC 3866 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3866 _ (by rfl)
    _ = 5105 := by rw [fixedPC3972]; rfl

@[simp] theorem fixedPC3974 : Artifact.submissionArtifact.instructionPC 3868 = 5107 := by
  calc
    Artifact.submissionArtifact.instructionPC 3868 =
        Artifact.submissionArtifact.instructionPC 3867 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3867 _ (by rfl)
    _ = 5107 := by rw [fixedPC3973]; rfl

@[simp] theorem fixedPC3975 : Artifact.submissionArtifact.instructionPC 3869 = 5108 := by
  calc
    Artifact.submissionArtifact.instructionPC 3869 =
        Artifact.submissionArtifact.instructionPC 3868 + (YulEvmCompiler.Instr.op .XOR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3868 _ (by rfl)
    _ = 5108 := by rw [fixedPC3974]; rfl

@[simp] theorem fixedPC3976 : Artifact.submissionArtifact.instructionPC 3870 = 5109 := by
  calc
    Artifact.submissionArtifact.instructionPC 3870 =
        Artifact.submissionArtifact.instructionPC 3869 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3869 _ (by rfl)
    _ = 5109 := by rw [fixedPC3975]; rfl

@[simp] theorem fixedPC3977 : Artifact.submissionArtifact.instructionPC 3871 = 5112 := by
  calc
    Artifact.submissionArtifact.instructionPC 3871 =
        Artifact.submissionArtifact.instructionPC 3870 + (YulEvmCompiler.Instr.push 2 5134).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3870 _ (by rfl)
    _ = 5112 := by rw [fixedPC3976]; rfl

@[simp] theorem fixedPC3978 : Artifact.submissionArtifact.instructionPC 3872 = 5113 := by
  calc
    Artifact.submissionArtifact.instructionPC 3872 =
        Artifact.submissionArtifact.instructionPC 3871 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3871 _ (by rfl)
    _ = 5113 := by rw [fixedPC3977]; rfl

@[simp] theorem fixedPC3979 : Artifact.submissionArtifact.instructionPC 3873 = 5114 := by
  calc
    Artifact.submissionArtifact.instructionPC 3873 =
        Artifact.submissionArtifact.instructionPC 3872 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3872 _ (by rfl)
    _ = 5114 := by rw [fixedPC3978]; rfl

@[simp] theorem fixedPC3980 : Artifact.submissionArtifact.instructionPC 3874 = 5116 := by
  calc
    Artifact.submissionArtifact.instructionPC 3874 =
        Artifact.submissionArtifact.instructionPC 3873 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3873 _ (by rfl)
    _ = 5116 := by rw [fixedPC3979]; rfl

@[simp] theorem fixedPC3981 : Artifact.submissionArtifact.instructionPC 3875 = 5117 := by
  calc
    Artifact.submissionArtifact.instructionPC 3875 =
        Artifact.submissionArtifact.instructionPC 3874 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3874 _ (by rfl)
    _ = 5117 := by rw [fixedPC3980]; rfl

@[simp] theorem fixedPC3982 : Artifact.submissionArtifact.instructionPC 3876 = 5118 := by
  calc
    Artifact.submissionArtifact.instructionPC 3876 =
        Artifact.submissionArtifact.instructionPC 3875 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3875 _ (by rfl)
    _ = 5118 := by rw [fixedPC3981]; rfl

@[simp] theorem fixedPC3983 : Artifact.submissionArtifact.instructionPC 3877 = 5119 := by
  calc
    Artifact.submissionArtifact.instructionPC 3877 =
        Artifact.submissionArtifact.instructionPC 3876 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3876 _ (by rfl)
    _ = 5119 := by rw [fixedPC3982]; rfl

@[simp] theorem fixedPC3984 : Artifact.submissionArtifact.instructionPC 3878 = 5120 := by
  calc
    Artifact.submissionArtifact.instructionPC 3878 =
        Artifact.submissionArtifact.instructionPC 3877 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3877 _ (by rfl)
    _ = 5120 := by rw [fixedPC3983]; rfl

@[simp] theorem fixedPC3985 : Artifact.submissionArtifact.instructionPC 3879 = 5123 := by
  calc
    Artifact.submissionArtifact.instructionPC 3879 =
        Artifact.submissionArtifact.instructionPC 3878 + (YulEvmCompiler.Instr.push 2 1186).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3878 _ (by rfl)
    _ = 5123 := by rw [fixedPC3984]; rfl

@[simp] theorem fixedPC3986 : Artifact.submissionArtifact.instructionPC 3880 = 5124 := by
  calc
    Artifact.submissionArtifact.instructionPC 3880 =
        Artifact.submissionArtifact.instructionPC 3879 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3879 _ (by rfl)
    _ = 5124 := by rw [fixedPC3985]; rfl

@[simp] theorem fixedPC3987 : Artifact.submissionArtifact.instructionPC 3881 = 5125 := by
  calc
    Artifact.submissionArtifact.instructionPC 3881 =
        Artifact.submissionArtifact.instructionPC 3880 + (YulEvmCompiler.Instr.op (.Dup ⟨3, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3880 _ (by rfl)
    _ = 5125 := by rw [fixedPC3986]; rfl

@[simp] theorem fixedPC3988 : Artifact.submissionArtifact.instructionPC 3882 = 5127 := by
  calc
    Artifact.submissionArtifact.instructionPC 3882 =
        Artifact.submissionArtifact.instructionPC 3881 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3881 _ (by rfl)
    _ = 5127 := by rw [fixedPC3987]; rfl

@[simp] theorem fixedPC3989 : Artifact.submissionArtifact.instructionPC 3883 = 5128 := by
  calc
    Artifact.submissionArtifact.instructionPC 3883 =
        Artifact.submissionArtifact.instructionPC 3882 + (YulEvmCompiler.Instr.op (.Dup ⟨6, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3882 _ (by rfl)
    _ = 5128 := by rw [fixedPC3988]; rfl

@[simp] theorem fixedPC3990 : Artifact.submissionArtifact.instructionPC 3884 = 5129 := by
  calc
    Artifact.submissionArtifact.instructionPC 3884 =
        Artifact.submissionArtifact.instructionPC 3883 + (YulEvmCompiler.Instr.op (.Dup ⟨8, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3883 _ (by rfl)
    _ = 5129 := by rw [fixedPC3989]; rfl

@[simp] theorem fixedPC3991 : Artifact.submissionArtifact.instructionPC 3885 = 5130 := by
  calc
    Artifact.submissionArtifact.instructionPC 3885 =
        Artifact.submissionArtifact.instructionPC 3884 + (YulEvmCompiler.Instr.op (.Dup ⟨10, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3884 _ (by rfl)
    _ = 5130 := by rw [fixedPC3990]; rfl

@[simp] theorem fixedPC3992 : Artifact.submissionArtifact.instructionPC 3886 = 5133 := by
  calc
    Artifact.submissionArtifact.instructionPC 3886 =
        Artifact.submissionArtifact.instructionPC 3885 + (YulEvmCompiler.Instr.push 2 4738).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3885 _ (by rfl)
    _ = 5133 := by rw [fixedPC3991]; rfl

@[simp] theorem fixedPC3993 : Artifact.submissionArtifact.instructionPC 3887 = 5134 := by
  calc
    Artifact.submissionArtifact.instructionPC 3887 =
        Artifact.submissionArtifact.instructionPC 3886 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3886 _ (by rfl)
    _ = 5134 := by rw [fixedPC3992]; rfl

@[simp] theorem fixedJump5272 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5134 = true := by
  simpa only [Artifact.instructionPC, fixedPC3993] using Artifact.isValidJumpDest_index 3887 (by rfl)

@[simp] theorem fixedPC3994 : Artifact.submissionArtifact.instructionPC 3888 = 5135 := by
  calc
    Artifact.submissionArtifact.instructionPC 3888 =
        Artifact.submissionArtifact.instructionPC 3887 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3887 _ (by rfl)
    _ = 5135 := by rw [fixedPC3993]; rfl

@[simp] theorem fixedPC3995 : Artifact.submissionArtifact.instructionPC 3889 = 5136 := by
  calc
    Artifact.submissionArtifact.instructionPC 3889 =
        Artifact.submissionArtifact.instructionPC 3888 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3888 _ (by rfl)
    _ = 5136 := by rw [fixedPC3994]; rfl

@[simp] theorem fixedPC3996 : Artifact.submissionArtifact.instructionPC 3890 = 5137 := by
  calc
    Artifact.submissionArtifact.instructionPC 3890 =
        Artifact.submissionArtifact.instructionPC 3889 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3889 _ (by rfl)
    _ = 5137 := by rw [fixedPC3995]; rfl

@[simp] theorem fixedPC3997 : Artifact.submissionArtifact.instructionPC 3891 = 5138 := by
  calc
    Artifact.submissionArtifact.instructionPC 3891 =
        Artifact.submissionArtifact.instructionPC 3890 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3890 _ (by rfl)
    _ = 5138 := by rw [fixedPC3996]; rfl

@[simp] theorem fixedPC3998 : Artifact.submissionArtifact.instructionPC 3892 = 5141 := by
  calc
    Artifact.submissionArtifact.instructionPC 3892 =
        Artifact.submissionArtifact.instructionPC 3891 + (YulEvmCompiler.Instr.push 2 1121).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3891 _ (by rfl)
    _ = 5141 := by rw [fixedPC3997]; rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3559 = 4664 := by
  decide

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4664 = true := by
  simpa only [Artifact.instructionPC, fixedPC3999] using Artifact.isValidJumpDest_index 3559 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3560 = 4665 := by
  calc
    Artifact.submissionArtifact.instructionPC 3560 =
        Artifact.submissionArtifact.instructionPC 3559 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3559 _ (by rfl)
    _ = 4665 := by rw [fixedPC3999]; rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3561 = 4668 := by
  calc
    Artifact.submissionArtifact.instructionPC 3561 =
        Artifact.submissionArtifact.instructionPC 3560 + (YulEvmCompiler.Instr.push 2 8352).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3560 _ (by rfl)
    _ = 4668 := by rw [fixedPC4000]; rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3562 = 4669 := by
  calc
    Artifact.submissionArtifact.instructionPC 3562 =
        Artifact.submissionArtifact.instructionPC 3561 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3561 _ (by rfl)
    _ = 4669 := by rw [fixedPC4001]; rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3563 = 4671 := by
  calc
    Artifact.submissionArtifact.instructionPC 3563 =
        Artifact.submissionArtifact.instructionPC 3562 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3562 _ (by rfl)
    _ = 4671 := by rw [fixedPC4002]; rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3564 = 4672 := by
  calc
    Artifact.submissionArtifact.instructionPC 3564 =
        Artifact.submissionArtifact.instructionPC 3563 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3563 _ (by rfl)
    _ = 4672 := by rw [fixedPC4003]; rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3565 = 4673 := by
  calc
    Artifact.submissionArtifact.instructionPC 3565 =
        Artifact.submissionArtifact.instructionPC 3564 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3564 _ (by rfl)
    _ = 4673 := by rw [fixedPC4004]; rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3566 = 4674 := by
  calc
    Artifact.submissionArtifact.instructionPC 3566 =
        Artifact.submissionArtifact.instructionPC 3565 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3565 _ (by rfl)
    _ = 4674 := by rw [fixedPC4005]; rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3567 = 4675 := by
  calc
    Artifact.submissionArtifact.instructionPC 3567 =
        Artifact.submissionArtifact.instructionPC 3566 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3566 _ (by rfl)
    _ = 4675 := by rw [fixedPC4006]; rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3568 = 4676 := by
  calc
    Artifact.submissionArtifact.instructionPC 3568 =
        Artifact.submissionArtifact.instructionPC 3567 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3567 _ (by rfl)
    _ = 4676 := by rw [fixedPC4007]; rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3569 = 4677 := by
  calc
    Artifact.submissionArtifact.instructionPC 3569 =
        Artifact.submissionArtifact.instructionPC 3568 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3568 _ (by rfl)
    _ = 4677 := by rw [fixedPC4008]; rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3570 = 4680 := by
  calc
    Artifact.submissionArtifact.instructionPC 3570 =
        Artifact.submissionArtifact.instructionPC 3569 + (YulEvmCompiler.Instr.push 2 7264).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3569 _ (by rfl)
    _ = 4680 := by rw [fixedPC4009]; rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3571 = 4681 := by
  calc
    Artifact.submissionArtifact.instructionPC 3571 =
        Artifact.submissionArtifact.instructionPC 3570 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3570 _ (by rfl)
    _ = 4681 := by rw [fixedPC4010]; rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3572 = 4684 := by
  calc
    Artifact.submissionArtifact.instructionPC 3572 =
        Artifact.submissionArtifact.instructionPC 3571 + (YulEvmCompiler.Instr.push 2 4979).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3571 _ (by rfl)
    _ = 4684 := by rw [fixedPC4011]; rfl


@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2759 = 3622 := by rfl
@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3545 = 4642 := by rfl
@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3546 = 4643 := by rfl
@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3547 = 4644 := by rfl
@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3548 = 4645 := by rfl
@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3549 = 4648 := by rfl
@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3550 = 4649 := by rfl
@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3551 = 4650 := by rfl
@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3552 = 4651 := by rfl
@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3553 = 4654 := by rfl
@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3554 = 4655 := by rfl
@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3555 = 4656 := by rfl
@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3556 = 4659 := by rfl
@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3557 = 4660 := by rfl
@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3558 = 4663 := by rfl
@[simp] theorem earlyExtraPC2927 : Artifact.submissionArtifact.instructionPC 2789 = 3653 := by rfl
@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3559 = 4664 := by rfl
@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3560 = 4665 := by rfl
@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3561 = 4668 := by rfl
@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3562 = 4669 := by rfl
@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3563 = 4671 := by rfl
@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3564 = 4672 := by rfl
@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3565 = 4673 := by rfl
@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3566 = 4674 := by rfl
@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3567 = 4675 := by rfl
@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3568 = 4676 := by rfl
@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3569 = 4677 := by rfl
@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3570 = 4680 := by rfl
@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3571 = 4681 := by rfl
@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3572 = 4684 := by rfl
@[simp] theorem earlyExtraPC3918 : Artifact.submissionArtifact.instructionPC 3833 = 5057 := by rfl
@[simp] theorem earlyExtraPC3919 : Artifact.submissionArtifact.instructionPC 3834 = 5058 := by rfl
@[simp] theorem earlyExtraPC3920 : Artifact.submissionArtifact.instructionPC 3835 = 5061 := by rfl
@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 3836 = 5062 := by rfl
@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 3837 = 5063 := by rfl
@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 3838 = 5066 := by rfl
@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 3839 = 5069 := by rfl
@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 3840 = 5070 := by rfl
@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 3841 = 5071 := by rfl
@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 3842 = 5072 := by rfl
@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 3843 = 5073 := by rfl
end Challenge.Modexp.Submission.Proofs.Fast
