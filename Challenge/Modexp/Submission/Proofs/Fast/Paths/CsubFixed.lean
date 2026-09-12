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
  [opAt 3677 .JUMPDEST,
   pushAt 3678 2 2784,
   opAt 3679 .MLOAD,
   pushAt 3680 2 256,
   opAt 3681 .EQ,
   pushAt 3682 2 4895,
   opAt 3683 .JUMPI,
   pushAt 3684 2 2784,
   opAt 3685 .MLOAD,
   pushAt 3686 1 128,
   opAt 3687 .EQ,
   pushAt 3688 2 4689,
   opAt 3689 .JUMPI,
   pushAt 3690 2 2880,
   opAt 3691 .MLOAD,
   pushAt 3692 2 2848,
   opAt 3693 .MLOAD,
   opAt 3694 (.Dup ⟨0, by decide⟩),
   pushAt 3695 2 1792,
   opAt 3696 .ADD,
   pushAt 3697 2 2112,
   opAt 3698 .POP,
   opAt 3699 (.Swap ⟨0, by decide⟩),
   pushAt 3700 0 0,
   opAt 3701 (.Swap ⟨2, by decide⟩),
   pushAt 3702 2 2026,
   opAt 3703 .JUMP]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3677 .JUMPDEST,
   pushAt 3678 2 2784,
   opAt 3679 .MLOAD,
   pushAt 3680 2 256,
   opAt 3681 .EQ,
   pushAt 3682 2 4895,
   opAt 3683 .JUMPI,
   opAt 3704 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3677 .JUMPDEST,
   pushAt 3678 2 2784,
   opAt 3679 .MLOAD,
   pushAt 3680 2 256,
   opAt 3681 .EQ,
   pushAt 3682 2 4895,
   opAt 3683 .JUMPI,
   pushAt 3684 2 2784,
   opAt 3685 .MLOAD,
   pushAt 3686 1 128,
   opAt 3687 .EQ,
   pushAt 3688 2 4689,
   opAt 3689 .JUMPI,
   opAt 3576 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3705 2 2336,
   opAt 3706 .MLOAD,
   pushAt 3707 1 224,
   opAt 3708 .MLOAD,
   opAt 3709 (.Dup ⟨1, by decide⟩),
   opAt 3710 (.Dup ⟨1, by decide⟩),
   opAt 3711 .GT,
   opAt 3712 (.Swap ⟨1, by decide⟩),
   opAt 3713 .SUB,
   pushAt 3714 2 2016,
   opAt 3715 .MSTORE]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3716 2 2304,
   opAt 3717 .MLOAD,
   pushAt 3718 1 192,
   opAt 3719 .MLOAD,
   opAt 3720 (.Dup ⟨1, by decide⟩),
   opAt 3721 (.Dup ⟨1, by decide⟩),
   opAt 3722 .GT,
   opAt 3723 (.Swap ⟨1, by decide⟩),
   opAt 3724 .SUB,
   opAt 3725 (.Dup ⟨2, by decide⟩),
   opAt 3726 (.Dup ⟨1, by decide⟩),
   opAt 3727 .SUB,
   opAt 3728 (.Swap ⟨2, by decide⟩),
   opAt 3729 .GT,
   opAt 3730 .OR,
   opAt 3731 (.Swap ⟨0, by decide⟩),
   pushAt 3732 2 1984,
   opAt 3733 .MSTORE]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3734 2 2272,
   opAt 3735 .MLOAD,
   pushAt 3736 1 160,
   opAt 3737 .MLOAD,
   opAt 3738 (.Dup ⟨1, by decide⟩),
   opAt 3739 (.Dup ⟨1, by decide⟩),
   opAt 3740 .GT,
   opAt 3741 (.Swap ⟨1, by decide⟩),
   opAt 3742 .SUB,
   opAt 3743 (.Dup ⟨2, by decide⟩),
   opAt 3744 (.Dup ⟨1, by decide⟩),
   opAt 3745 .SUB,
   opAt 3746 (.Swap ⟨2, by decide⟩),
   opAt 3747 .GT,
   opAt 3748 .OR,
   opAt 3749 (.Swap ⟨0, by decide⟩),
   pushAt 3750 2 1952,
   opAt 3751 .MSTORE]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3752 2 2240,
   opAt 3753 .MLOAD,
   pushAt 3754 1 128,
   opAt 3755 .MLOAD,
   opAt 3756 (.Dup ⟨1, by decide⟩),
   opAt 3757 (.Dup ⟨1, by decide⟩),
   opAt 3758 .GT,
   opAt 3759 (.Swap ⟨1, by decide⟩),
   opAt 3760 .SUB,
   opAt 3761 (.Dup ⟨2, by decide⟩),
   opAt 3762 (.Dup ⟨1, by decide⟩),
   opAt 3763 .SUB,
   opAt 3764 (.Swap ⟨2, by decide⟩),
   opAt 3765 .GT,
   opAt 3766 .OR,
   opAt 3767 (.Swap ⟨0, by decide⟩),
   pushAt 3768 2 1920,
   opAt 3769 .MSTORE]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 3770 2 2208,
   opAt 3771 .MLOAD,
   pushAt 3772 1 96,
   opAt 3773 .MLOAD,
   opAt 3774 (.Dup ⟨1, by decide⟩),
   opAt 3775 (.Dup ⟨1, by decide⟩),
   opAt 3776 .GT,
   opAt 3777 (.Swap ⟨1, by decide⟩),
   opAt 3778 .SUB,
   opAt 3779 (.Dup ⟨2, by decide⟩),
   opAt 3780 (.Dup ⟨1, by decide⟩),
   opAt 3781 .SUB,
   opAt 3782 (.Swap ⟨2, by decide⟩),
   opAt 3783 .GT,
   opAt 3784 .OR,
   opAt 3785 (.Swap ⟨0, by decide⟩),
   pushAt 3786 2 1888,
   opAt 3787 .MSTORE]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3788 .JUMPDEST,
   pushAt 3789 2 2176,
   opAt 3790 .MLOAD,
   pushAt 3791 1 64,
   opAt 3792 .MLOAD,
   opAt 3793 (.Dup ⟨1, by decide⟩),
   opAt 3794 (.Dup ⟨1, by decide⟩),
   opAt 3795 .GT,
   opAt 3796 (.Swap ⟨1, by decide⟩),
   opAt 3797 .SUB,
   opAt 3798 (.Dup ⟨2, by decide⟩),
   opAt 3799 (.Dup ⟨1, by decide⟩),
   opAt 3800 .SUB,
   opAt 3801 (.Swap ⟨2, by decide⟩),
   opAt 3802 .GT,
   opAt 3803 .OR,
   opAt 3804 (.Swap ⟨0, by decide⟩),
   pushAt 3805 2 1856,
   opAt 3806 .MSTORE]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3807 2 2144,
   opAt 3808 .MLOAD,
   pushAt 3809 1 32,
   opAt 3810 .MLOAD,
   opAt 3811 (.Dup ⟨1, by decide⟩),
   opAt 3812 (.Dup ⟨1, by decide⟩),
   opAt 3813 .GT,
   opAt 3814 (.Swap ⟨1, by decide⟩),
   opAt 3815 .SUB,
   opAt 3816 (.Dup ⟨2, by decide⟩),
   opAt 3817 (.Dup ⟨1, by decide⟩),
   opAt 3818 .SUB,
   opAt 3819 (.Swap ⟨2, by decide⟩),
   opAt 3820 .GT,
   opAt 3821 .OR,
   opAt 3822 (.Swap ⟨0, by decide⟩),
   pushAt 3823 2 1824,
   opAt 3824 .MSTORE]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3825 2 2112,
   opAt 3826 .MLOAD,
   pushAt 3827 0 0,
   opAt 3828 .MLOAD,
   opAt 3829 (.Dup ⟨1, by decide⟩),
   opAt 3830 (.Dup ⟨1, by decide⟩),
   opAt 3831 .GT,
   opAt 3832 (.Swap ⟨1, by decide⟩),
   opAt 3833 .SUB,
   opAt 3834 (.Dup ⟨2, by decide⟩),
   opAt 3835 (.Dup ⟨1, by decide⟩),
   opAt 3836 .SUB,
   opAt 3837 (.Swap ⟨2, by decide⟩),
   opAt 3838 .GT,
   opAt 3839 .OR,
   opAt 3840 (.Swap ⟨0, by decide⟩),
   pushAt 3841 2 1792,
   opAt 3842 .MSTORE]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3843 .ISZERO,
   pushAt 3844 2 2080,
   opAt 3845 .MLOAD,
   opAt 3846 .OR,
   pushAt 3847 2 319,
   opAt 3848 .NOT,
   pushAt 3849 2 5098,
   opAt 3850 .JUMP,
   opAt 3858 .JUMPDEST,
   opAt 3859 .MUL,
   pushAt 3860 2 2112,
   opAt 3861 .ADD,
   pushAt 3862 2 2784,
   opAt 3863 .MLOAD,
   opAt 3864 (.Swap ⟨1, by decide⟩),
   opAt 3865 .MCOPY,
   opAt 3866 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3577 2 2208,
   opAt 3578 .MLOAD,
   pushAt 3579 1 96,
   opAt 3580 .MLOAD,
   opAt 3581 (.Dup ⟨1, by decide⟩),
   opAt 3582 (.Dup ⟨1, by decide⟩),
   opAt 3583 .GT,
   opAt 3584 (.Swap ⟨1, by decide⟩),
   opAt 3585 .SUB,
   pushAt 3586 2 1888,
   opAt 3587 .MSTORE,
   pushAt 3588 2 5004,
   opAt 3589 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3788 .JUMPDEST,
   pushAt 3789 2 2176,
   opAt 3790 .MLOAD,
   pushAt 3791 1 64,
   opAt 3792 .MLOAD,
   opAt 3793 (.Dup ⟨1, by decide⟩),
   opAt 3794 (.Dup ⟨1, by decide⟩),
   opAt 3795 .GT,
   opAt 3796 (.Swap ⟨1, by decide⟩),
   opAt 3797 .SUB,
   opAt 3798 (.Dup ⟨2, by decide⟩),
   opAt 3799 (.Dup ⟨1, by decide⟩),
   opAt 3800 .SUB,
   opAt 3801 (.Swap ⟨2, by decide⟩),
   opAt 3802 .GT,
   opAt 3803 .OR,
   opAt 3804 (.Swap ⟨0, by decide⟩),
   pushAt 3805 2 1856,
   opAt 3806 .MSTORE]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3807 2 2144,
   opAt 3808 .MLOAD,
   pushAt 3809 1 32,
   opAt 3810 .MLOAD,
   opAt 3811 (.Dup ⟨1, by decide⟩),
   opAt 3812 (.Dup ⟨1, by decide⟩),
   opAt 3813 .GT,
   opAt 3814 (.Swap ⟨1, by decide⟩),
   opAt 3815 .SUB,
   opAt 3816 (.Dup ⟨2, by decide⟩),
   opAt 3817 (.Dup ⟨1, by decide⟩),
   opAt 3818 .SUB,
   opAt 3819 (.Swap ⟨2, by decide⟩),
   opAt 3820 .GT,
   opAt 3821 .OR,
   opAt 3822 (.Swap ⟨0, by decide⟩),
   pushAt 3823 2 1824,
   opAt 3824 .MSTORE]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3825 2 2112,
   opAt 3826 .MLOAD,
   pushAt 3827 0 0,
   opAt 3828 .MLOAD,
   opAt 3829 (.Dup ⟨1, by decide⟩),
   opAt 3830 (.Dup ⟨1, by decide⟩),
   opAt 3831 .GT,
   opAt 3832 (.Swap ⟨1, by decide⟩),
   opAt 3833 .SUB,
   opAt 3834 (.Dup ⟨2, by decide⟩),
   opAt 3835 (.Dup ⟨1, by decide⟩),
   opAt 3836 .SUB,
   opAt 3837 (.Swap ⟨2, by decide⟩),
   opAt 3838 .GT,
   opAt 3839 .OR,
   opAt 3840 (.Swap ⟨0, by decide⟩),
   pushAt 3841 2 1792,
   opAt 3842 .MSTORE]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3843 .ISZERO,
   pushAt 3844 2 2080,
   opAt 3845 .MLOAD,
   opAt 3846 .OR,
   pushAt 3847 2 319,
   opAt 3848 .NOT,
   pushAt 3849 2 5098,
   opAt 3850 .JUMP,
   opAt 3858 .JUMPDEST,
   opAt 3859 .MUL,
   pushAt 3860 2 2112,
   opAt 3861 .ADD,
   pushAt 3862 2 2784,
   opAt 3863 .MLOAD,
   opAt 3864 (.Swap ⟨1, by decide⟩),
   opAt 3865 .MCOPY,
   opAt 3866 .JUMP]

@[simp] theorem csubPC3576 : Artifact.submissionArtifact.instructionPC 3576 = 4689 := by rfl

@[simp] theorem csubPC3577 : Artifact.submissionArtifact.instructionPC 3577 = 4690 := by
  calc
    Artifact.submissionArtifact.instructionPC 3577 =
        Artifact.submissionArtifact.instructionPC 3576 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3576 _ (by rfl)
    _ = 4690 := by rw [csubPC3576]; rfl

@[simp] theorem csubPC3578 : Artifact.submissionArtifact.instructionPC 3578 = 4693 := by
  calc
    Artifact.submissionArtifact.instructionPC 3578 =
        Artifact.submissionArtifact.instructionPC 3577 + (YulEvmCompiler.Instr.push 2 2208).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3577 _ (by rfl)
    _ = 4693 := by rw [csubPC3577]; rfl

@[simp] theorem csubPC3579 : Artifact.submissionArtifact.instructionPC 3579 = 4694 := by
  calc
    Artifact.submissionArtifact.instructionPC 3579 =
        Artifact.submissionArtifact.instructionPC 3578 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3578 _ (by rfl)
    _ = 4694 := by rw [csubPC3578]; rfl

@[simp] theorem csubPC3580 : Artifact.submissionArtifact.instructionPC 3580 = 4696 := by
  calc
    Artifact.submissionArtifact.instructionPC 3580 =
        Artifact.submissionArtifact.instructionPC 3579 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3579 _ (by rfl)
    _ = 4696 := by rw [csubPC3579]; rfl

@[simp] theorem csubPC3581 : Artifact.submissionArtifact.instructionPC 3581 = 4697 := by
  calc
    Artifact.submissionArtifact.instructionPC 3581 =
        Artifact.submissionArtifact.instructionPC 3580 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3580 _ (by rfl)
    _ = 4697 := by rw [csubPC3580]; rfl

@[simp] theorem csubPC3582 : Artifact.submissionArtifact.instructionPC 3582 = 4698 := by
  calc
    Artifact.submissionArtifact.instructionPC 3582 =
        Artifact.submissionArtifact.instructionPC 3581 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3581 _ (by rfl)
    _ = 4698 := by rw [csubPC3581]; rfl

@[simp] theorem csubPC3583 : Artifact.submissionArtifact.instructionPC 3583 = 4699 := by
  calc
    Artifact.submissionArtifact.instructionPC 3583 =
        Artifact.submissionArtifact.instructionPC 3582 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3582 _ (by rfl)
    _ = 4699 := by rw [csubPC3582]; rfl

@[simp] theorem csubPC3584 : Artifact.submissionArtifact.instructionPC 3584 = 4700 := by
  calc
    Artifact.submissionArtifact.instructionPC 3584 =
        Artifact.submissionArtifact.instructionPC 3583 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3583 _ (by rfl)
    _ = 4700 := by rw [csubPC3583]; rfl

@[simp] theorem csubPC3585 : Artifact.submissionArtifact.instructionPC 3585 = 4701 := by
  calc
    Artifact.submissionArtifact.instructionPC 3585 =
        Artifact.submissionArtifact.instructionPC 3584 + (YulEvmCompiler.Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3584 _ (by rfl)
    _ = 4701 := by rw [csubPC3584]; rfl

@[simp] theorem csubPC3586 : Artifact.submissionArtifact.instructionPC 3586 = 4702 := by
  calc
    Artifact.submissionArtifact.instructionPC 3586 =
        Artifact.submissionArtifact.instructionPC 3585 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3585 _ (by rfl)
    _ = 4702 := by rw [csubPC3585]; rfl

@[simp] theorem csubPC3587 : Artifact.submissionArtifact.instructionPC 3587 = 4705 := by
  calc
    Artifact.submissionArtifact.instructionPC 3587 =
        Artifact.submissionArtifact.instructionPC 3586 + (YulEvmCompiler.Instr.push 2 1888).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3586 _ (by rfl)
    _ = 4705 := by rw [csubPC3586]; rfl

@[simp] theorem csubPC3588 : Artifact.submissionArtifact.instructionPC 3588 = 4706 := by
  calc
    Artifact.submissionArtifact.instructionPC 3588 =
        Artifact.submissionArtifact.instructionPC 3587 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3587 _ (by rfl)
    _ = 4706 := by rw [csubPC3587]; rfl

@[simp] theorem csubPC3589 : Artifact.submissionArtifact.instructionPC 3589 = 4709 := by
  calc
    Artifact.submissionArtifact.instructionPC 3589 =
        Artifact.submissionArtifact.instructionPC 3588 + (YulEvmCompiler.Instr.push 2 5004).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3588 _ (by rfl)
    _ = 4709 := by rw [csubPC3588]; rfl

@[simp] theorem csubPC3677 : Artifact.submissionArtifact.instructionPC 3677 = 4847 := by rfl

@[simp] theorem csubPC3678 : Artifact.submissionArtifact.instructionPC 3678 = 4848 := by
  calc
    Artifact.submissionArtifact.instructionPC 3678 =
        Artifact.submissionArtifact.instructionPC 3677 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3677 _ (by rfl)
    _ = 4848 := by rw [csubPC3677]; rfl

@[simp] theorem csubPC3679 : Artifact.submissionArtifact.instructionPC 3679 = 4851 := by
  calc
    Artifact.submissionArtifact.instructionPC 3679 =
        Artifact.submissionArtifact.instructionPC 3678 + (YulEvmCompiler.Instr.push 2 2784).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3678 _ (by rfl)
    _ = 4851 := by rw [csubPC3678]; rfl

@[simp] theorem csubPC3680 : Artifact.submissionArtifact.instructionPC 3680 = 4852 := by
  calc
    Artifact.submissionArtifact.instructionPC 3680 =
        Artifact.submissionArtifact.instructionPC 3679 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3679 _ (by rfl)
    _ = 4852 := by rw [csubPC3679]; rfl

@[simp] theorem csubPC3681 : Artifact.submissionArtifact.instructionPC 3681 = 4855 := by
  calc
    Artifact.submissionArtifact.instructionPC 3681 =
        Artifact.submissionArtifact.instructionPC 3680 + (YulEvmCompiler.Instr.push 2 256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3680 _ (by rfl)
    _ = 4855 := by rw [csubPC3680]; rfl

@[simp] theorem csubPC3682 : Artifact.submissionArtifact.instructionPC 3682 = 4856 := by
  calc
    Artifact.submissionArtifact.instructionPC 3682 =
        Artifact.submissionArtifact.instructionPC 3681 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3681 _ (by rfl)
    _ = 4856 := by rw [csubPC3681]; rfl

@[simp] theorem csubPC3683 : Artifact.submissionArtifact.instructionPC 3683 = 4859 := by
  calc
    Artifact.submissionArtifact.instructionPC 3683 =
        Artifact.submissionArtifact.instructionPC 3682 + (YulEvmCompiler.Instr.push 2 4895).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3682 _ (by rfl)
    _ = 4859 := by rw [csubPC3682]; rfl

@[simp] theorem csubPC3684 : Artifact.submissionArtifact.instructionPC 3684 = 4860 := by
  calc
    Artifact.submissionArtifact.instructionPC 3684 =
        Artifact.submissionArtifact.instructionPC 3683 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3683 _ (by rfl)
    _ = 4860 := by rw [csubPC3683]; rfl

@[simp] theorem csubPC3685 : Artifact.submissionArtifact.instructionPC 3685 = 4863 := by
  calc
    Artifact.submissionArtifact.instructionPC 3685 =
        Artifact.submissionArtifact.instructionPC 3684 + (YulEvmCompiler.Instr.push 2 2784).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3684 _ (by rfl)
    _ = 4863 := by rw [csubPC3684]; rfl

@[simp] theorem csubPC3686 : Artifact.submissionArtifact.instructionPC 3686 = 4864 := by
  calc
    Artifact.submissionArtifact.instructionPC 3686 =
        Artifact.submissionArtifact.instructionPC 3685 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3685 _ (by rfl)
    _ = 4864 := by rw [csubPC3685]; rfl

@[simp] theorem csubPC3687 : Artifact.submissionArtifact.instructionPC 3687 = 4866 := by
  calc
    Artifact.submissionArtifact.instructionPC 3687 =
        Artifact.submissionArtifact.instructionPC 3686 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3686 _ (by rfl)
    _ = 4866 := by rw [csubPC3686]; rfl

@[simp] theorem csubPC3688 : Artifact.submissionArtifact.instructionPC 3688 = 4867 := by
  calc
    Artifact.submissionArtifact.instructionPC 3688 =
        Artifact.submissionArtifact.instructionPC 3687 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3687 _ (by rfl)
    _ = 4867 := by rw [csubPC3687]; rfl

@[simp] theorem csubPC3689 : Artifact.submissionArtifact.instructionPC 3689 = 4870 := by
  calc
    Artifact.submissionArtifact.instructionPC 3689 =
        Artifact.submissionArtifact.instructionPC 3688 + (YulEvmCompiler.Instr.push 2 4689).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3688 _ (by rfl)
    _ = 4870 := by rw [csubPC3688]; rfl

@[simp] theorem csubPC3690 : Artifact.submissionArtifact.instructionPC 3690 = 4871 := by
  calc
    Artifact.submissionArtifact.instructionPC 3690 =
        Artifact.submissionArtifact.instructionPC 3689 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3689 _ (by rfl)
    _ = 4871 := by rw [csubPC3689]; rfl

@[simp] theorem csubPC3691 : Artifact.submissionArtifact.instructionPC 3691 = 4874 := by
  calc
    Artifact.submissionArtifact.instructionPC 3691 =
        Artifact.submissionArtifact.instructionPC 3690 + (YulEvmCompiler.Instr.push 2 2880).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3690 _ (by rfl)
    _ = 4874 := by rw [csubPC3690]; rfl

@[simp] theorem csubPC3692 : Artifact.submissionArtifact.instructionPC 3692 = 4875 := by
  calc
    Artifact.submissionArtifact.instructionPC 3692 =
        Artifact.submissionArtifact.instructionPC 3691 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3691 _ (by rfl)
    _ = 4875 := by rw [csubPC3691]; rfl

@[simp] theorem csubPC3693 : Artifact.submissionArtifact.instructionPC 3693 = 4878 := by
  calc
    Artifact.submissionArtifact.instructionPC 3693 =
        Artifact.submissionArtifact.instructionPC 3692 + (YulEvmCompiler.Instr.push 2 2848).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3692 _ (by rfl)
    _ = 4878 := by rw [csubPC3692]; rfl

@[simp] theorem csubPC3694 : Artifact.submissionArtifact.instructionPC 3694 = 4879 := by
  calc
    Artifact.submissionArtifact.instructionPC 3694 =
        Artifact.submissionArtifact.instructionPC 3693 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3693 _ (by rfl)
    _ = 4879 := by rw [csubPC3693]; rfl

@[simp] theorem csubPC3695 : Artifact.submissionArtifact.instructionPC 3695 = 4880 := by
  calc
    Artifact.submissionArtifact.instructionPC 3695 =
        Artifact.submissionArtifact.instructionPC 3694 + (YulEvmCompiler.Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3694 _ (by rfl)
    _ = 4880 := by rw [csubPC3694]; rfl

@[simp] theorem csubPC3696 : Artifact.submissionArtifact.instructionPC 3696 = 4883 := by
  calc
    Artifact.submissionArtifact.instructionPC 3696 =
        Artifact.submissionArtifact.instructionPC 3695 + (YulEvmCompiler.Instr.push 2 1792).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3695 _ (by rfl)
    _ = 4883 := by rw [csubPC3695]; rfl

@[simp] theorem csubPC3697 : Artifact.submissionArtifact.instructionPC 3697 = 4884 := by
  calc
    Artifact.submissionArtifact.instructionPC 3697 =
        Artifact.submissionArtifact.instructionPC 3696 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3696 _ (by rfl)
    _ = 4884 := by rw [csubPC3696]; rfl

@[simp] theorem csubPC3698 : Artifact.submissionArtifact.instructionPC 3698 = 4887 := by
  calc
    Artifact.submissionArtifact.instructionPC 3698 =
        Artifact.submissionArtifact.instructionPC 3697 + (YulEvmCompiler.Instr.push 2 2112).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3697 _ (by rfl)
    _ = 4887 := by rw [csubPC3697]; rfl

@[simp] theorem csubPC3699 : Artifact.submissionArtifact.instructionPC 3699 = 4888 := by
  calc
    Artifact.submissionArtifact.instructionPC 3699 =
        Artifact.submissionArtifact.instructionPC 3698 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3698 _ (by rfl)
    _ = 4888 := by rw [csubPC3698]; rfl

@[simp] theorem csubPC3700 : Artifact.submissionArtifact.instructionPC 3700 = 4889 := by
  calc
    Artifact.submissionArtifact.instructionPC 3700 =
        Artifact.submissionArtifact.instructionPC 3699 + (YulEvmCompiler.Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3699 _ (by rfl)
    _ = 4889 := by rw [csubPC3699]; rfl

@[simp] theorem csubPC3701 : Artifact.submissionArtifact.instructionPC 3701 = 4890 := by
  calc
    Artifact.submissionArtifact.instructionPC 3701 =
        Artifact.submissionArtifact.instructionPC 3700 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3700 _ (by rfl)
    _ = 4890 := by rw [csubPC3700]; rfl

@[simp] theorem csubPC3702 : Artifact.submissionArtifact.instructionPC 3702 = 4891 := by
  calc
    Artifact.submissionArtifact.instructionPC 3702 =
        Artifact.submissionArtifact.instructionPC 3701 + (YulEvmCompiler.Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3701 _ (by rfl)
    _ = 4891 := by rw [csubPC3701]; rfl

@[simp] theorem csubPC3703 : Artifact.submissionArtifact.instructionPC 3703 = 4894 := by
  calc
    Artifact.submissionArtifact.instructionPC 3703 =
        Artifact.submissionArtifact.instructionPC 3702 + (YulEvmCompiler.Instr.push 2 2026).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3702 _ (by rfl)
    _ = 4894 := by rw [csubPC3702]; rfl

@[simp] theorem csubPC3704 : Artifact.submissionArtifact.instructionPC 3704 = 4895 := by
  calc
    Artifact.submissionArtifact.instructionPC 3704 =
        Artifact.submissionArtifact.instructionPC 3703 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3703 _ (by rfl)
    _ = 4895 := by rw [csubPC3703]; rfl

@[simp] theorem csubPC3705 : Artifact.submissionArtifact.instructionPC 3705 = 4896 := by
  calc
    Artifact.submissionArtifact.instructionPC 3705 =
        Artifact.submissionArtifact.instructionPC 3704 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3704 _ (by rfl)
    _ = 4896 := by rw [csubPC3704]; rfl

@[simp] theorem csubPC3706 : Artifact.submissionArtifact.instructionPC 3706 = 4899 := by
  calc
    Artifact.submissionArtifact.instructionPC 3706 =
        Artifact.submissionArtifact.instructionPC 3705 + (YulEvmCompiler.Instr.push 2 2336).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3705 _ (by rfl)
    _ = 4899 := by rw [csubPC3705]; rfl

@[simp] theorem csubPC3707 : Artifact.submissionArtifact.instructionPC 3707 = 4900 := by
  calc
    Artifact.submissionArtifact.instructionPC 3707 =
        Artifact.submissionArtifact.instructionPC 3706 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3706 _ (by rfl)
    _ = 4900 := by rw [csubPC3706]; rfl

@[simp] theorem csubPC3708 : Artifact.submissionArtifact.instructionPC 3708 = 4902 := by
  calc
    Artifact.submissionArtifact.instructionPC 3708 =
        Artifact.submissionArtifact.instructionPC 3707 + (YulEvmCompiler.Instr.push 1 224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3707 _ (by rfl)
    _ = 4902 := by rw [csubPC3707]; rfl

@[simp] theorem csubPC3709 : Artifact.submissionArtifact.instructionPC 3709 = 4903 := by
  calc
    Artifact.submissionArtifact.instructionPC 3709 =
        Artifact.submissionArtifact.instructionPC 3708 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3708 _ (by rfl)
    _ = 4903 := by rw [csubPC3708]; rfl

@[simp] theorem csubPC3710 : Artifact.submissionArtifact.instructionPC 3710 = 4904 := by
  calc
    Artifact.submissionArtifact.instructionPC 3710 =
        Artifact.submissionArtifact.instructionPC 3709 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3709 _ (by rfl)
    _ = 4904 := by rw [csubPC3709]; rfl

@[simp] theorem csubPC3711 : Artifact.submissionArtifact.instructionPC 3711 = 4905 := by
  calc
    Artifact.submissionArtifact.instructionPC 3711 =
        Artifact.submissionArtifact.instructionPC 3710 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3710 _ (by rfl)
    _ = 4905 := by rw [csubPC3710]; rfl

@[simp] theorem csubPC3712 : Artifact.submissionArtifact.instructionPC 3712 = 4906 := by
  calc
    Artifact.submissionArtifact.instructionPC 3712 =
        Artifact.submissionArtifact.instructionPC 3711 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3711 _ (by rfl)
    _ = 4906 := by rw [csubPC3711]; rfl

@[simp] theorem csubPC3713 : Artifact.submissionArtifact.instructionPC 3713 = 4907 := by
  calc
    Artifact.submissionArtifact.instructionPC 3713 =
        Artifact.submissionArtifact.instructionPC 3712 + (YulEvmCompiler.Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3712 _ (by rfl)
    _ = 4907 := by rw [csubPC3712]; rfl

@[simp] theorem csubPC3714 : Artifact.submissionArtifact.instructionPC 3714 = 4908 := by
  calc
    Artifact.submissionArtifact.instructionPC 3714 =
        Artifact.submissionArtifact.instructionPC 3713 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3713 _ (by rfl)
    _ = 4908 := by rw [csubPC3713]; rfl

@[simp] theorem csubPC3715 : Artifact.submissionArtifact.instructionPC 3715 = 4911 := by
  calc
    Artifact.submissionArtifact.instructionPC 3715 =
        Artifact.submissionArtifact.instructionPC 3714 + (YulEvmCompiler.Instr.push 2 2016).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3714 _ (by rfl)
    _ = 4911 := by rw [csubPC3714]; rfl

@[simp] theorem csubPC3716 : Artifact.submissionArtifact.instructionPC 3716 = 4912 := by
  calc
    Artifact.submissionArtifact.instructionPC 3716 =
        Artifact.submissionArtifact.instructionPC 3715 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3715 _ (by rfl)
    _ = 4912 := by rw [csubPC3715]; rfl

@[simp] theorem csubPC3717 : Artifact.submissionArtifact.instructionPC 3717 = 4915 := by
  calc
    Artifact.submissionArtifact.instructionPC 3717 =
        Artifact.submissionArtifact.instructionPC 3716 + (YulEvmCompiler.Instr.push 2 2304).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3716 _ (by rfl)
    _ = 4915 := by rw [csubPC3716]; rfl

@[simp] theorem csubPC3718 : Artifact.submissionArtifact.instructionPC 3718 = 4916 := by
  calc
    Artifact.submissionArtifact.instructionPC 3718 =
        Artifact.submissionArtifact.instructionPC 3717 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3717 _ (by rfl)
    _ = 4916 := by rw [csubPC3717]; rfl

@[simp] theorem csubPC3719 : Artifact.submissionArtifact.instructionPC 3719 = 4918 := by
  calc
    Artifact.submissionArtifact.instructionPC 3719 =
        Artifact.submissionArtifact.instructionPC 3718 + (YulEvmCompiler.Instr.push 1 192).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3718 _ (by rfl)
    _ = 4918 := by rw [csubPC3718]; rfl

@[simp] theorem csubPC3720 : Artifact.submissionArtifact.instructionPC 3720 = 4919 := by
  calc
    Artifact.submissionArtifact.instructionPC 3720 =
        Artifact.submissionArtifact.instructionPC 3719 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3719 _ (by rfl)
    _ = 4919 := by rw [csubPC3719]; rfl

@[simp] theorem csubPC3721 : Artifact.submissionArtifact.instructionPC 3721 = 4920 := by
  calc
    Artifact.submissionArtifact.instructionPC 3721 =
        Artifact.submissionArtifact.instructionPC 3720 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3720 _ (by rfl)
    _ = 4920 := by rw [csubPC3720]; rfl

@[simp] theorem csubPC3722 : Artifact.submissionArtifact.instructionPC 3722 = 4921 := by
  calc
    Artifact.submissionArtifact.instructionPC 3722 =
        Artifact.submissionArtifact.instructionPC 3721 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3721 _ (by rfl)
    _ = 4921 := by rw [csubPC3721]; rfl

@[simp] theorem csubPC3723 : Artifact.submissionArtifact.instructionPC 3723 = 4922 := by
  calc
    Artifact.submissionArtifact.instructionPC 3723 =
        Artifact.submissionArtifact.instructionPC 3722 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3722 _ (by rfl)
    _ = 4922 := by rw [csubPC3722]; rfl

@[simp] theorem csubPC3724 : Artifact.submissionArtifact.instructionPC 3724 = 4923 := by
  calc
    Artifact.submissionArtifact.instructionPC 3724 =
        Artifact.submissionArtifact.instructionPC 3723 + (YulEvmCompiler.Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3723 _ (by rfl)
    _ = 4923 := by rw [csubPC3723]; rfl

@[simp] theorem csubPC3725 : Artifact.submissionArtifact.instructionPC 3725 = 4924 := by
  calc
    Artifact.submissionArtifact.instructionPC 3725 =
        Artifact.submissionArtifact.instructionPC 3724 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3724 _ (by rfl)
    _ = 4924 := by rw [csubPC3724]; rfl

@[simp] theorem csubPC3726 : Artifact.submissionArtifact.instructionPC 3726 = 4925 := by
  calc
    Artifact.submissionArtifact.instructionPC 3726 =
        Artifact.submissionArtifact.instructionPC 3725 + (YulEvmCompiler.Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3725 _ (by rfl)
    _ = 4925 := by rw [csubPC3725]; rfl

@[simp] theorem csubPC3727 : Artifact.submissionArtifact.instructionPC 3727 = 4926 := by
  calc
    Artifact.submissionArtifact.instructionPC 3727 =
        Artifact.submissionArtifact.instructionPC 3726 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3726 _ (by rfl)
    _ = 4926 := by rw [csubPC3726]; rfl

@[simp] theorem csubPC3728 : Artifact.submissionArtifact.instructionPC 3728 = 4927 := by
  calc
    Artifact.submissionArtifact.instructionPC 3728 =
        Artifact.submissionArtifact.instructionPC 3727 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3727 _ (by rfl)
    _ = 4927 := by rw [csubPC3727]; rfl

@[simp] theorem csubPC3729 : Artifact.submissionArtifact.instructionPC 3729 = 4928 := by
  calc
    Artifact.submissionArtifact.instructionPC 3729 =
        Artifact.submissionArtifact.instructionPC 3728 + (YulEvmCompiler.Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3728 _ (by rfl)
    _ = 4928 := by rw [csubPC3728]; rfl

@[simp] theorem csubPC3730 : Artifact.submissionArtifact.instructionPC 3730 = 4929 := by
  calc
    Artifact.submissionArtifact.instructionPC 3730 =
        Artifact.submissionArtifact.instructionPC 3729 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3729 _ (by rfl)
    _ = 4929 := by rw [csubPC3729]; rfl

@[simp] theorem csubPC3731 : Artifact.submissionArtifact.instructionPC 3731 = 4930 := by
  calc
    Artifact.submissionArtifact.instructionPC 3731 =
        Artifact.submissionArtifact.instructionPC 3730 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3730 _ (by rfl)
    _ = 4930 := by rw [csubPC3730]; rfl

@[simp] theorem csubPC3732 : Artifact.submissionArtifact.instructionPC 3732 = 4931 := by
  calc
    Artifact.submissionArtifact.instructionPC 3732 =
        Artifact.submissionArtifact.instructionPC 3731 + (YulEvmCompiler.Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3731 _ (by rfl)
    _ = 4931 := by rw [csubPC3731]; rfl

@[simp] theorem csubPC3733 : Artifact.submissionArtifact.instructionPC 3733 = 4934 := by
  calc
    Artifact.submissionArtifact.instructionPC 3733 =
        Artifact.submissionArtifact.instructionPC 3732 + (YulEvmCompiler.Instr.push 2 1984).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3732 _ (by rfl)
    _ = 4934 := by rw [csubPC3732]; rfl

@[simp] theorem csubPC3734 : Artifact.submissionArtifact.instructionPC 3734 = 4935 := by
  calc
    Artifact.submissionArtifact.instructionPC 3734 =
        Artifact.submissionArtifact.instructionPC 3733 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3733 _ (by rfl)
    _ = 4935 := by rw [csubPC3733]; rfl

@[simp] theorem csubPC3735 : Artifact.submissionArtifact.instructionPC 3735 = 4938 := by
  calc
    Artifact.submissionArtifact.instructionPC 3735 =
        Artifact.submissionArtifact.instructionPC 3734 + (YulEvmCompiler.Instr.push 2 2272).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3734 _ (by rfl)
    _ = 4938 := by rw [csubPC3734]; rfl

@[simp] theorem csubPC3736 : Artifact.submissionArtifact.instructionPC 3736 = 4939 := by
  calc
    Artifact.submissionArtifact.instructionPC 3736 =
        Artifact.submissionArtifact.instructionPC 3735 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3735 _ (by rfl)
    _ = 4939 := by rw [csubPC3735]; rfl

@[simp] theorem csubPC3737 : Artifact.submissionArtifact.instructionPC 3737 = 4941 := by
  calc
    Artifact.submissionArtifact.instructionPC 3737 =
        Artifact.submissionArtifact.instructionPC 3736 + (YulEvmCompiler.Instr.push 1 160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3736 _ (by rfl)
    _ = 4941 := by rw [csubPC3736]; rfl

@[simp] theorem csubPC3738 : Artifact.submissionArtifact.instructionPC 3738 = 4942 := by
  calc
    Artifact.submissionArtifact.instructionPC 3738 =
        Artifact.submissionArtifact.instructionPC 3737 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3737 _ (by rfl)
    _ = 4942 := by rw [csubPC3737]; rfl

@[simp] theorem csubPC3739 : Artifact.submissionArtifact.instructionPC 3739 = 4943 := by
  calc
    Artifact.submissionArtifact.instructionPC 3739 =
        Artifact.submissionArtifact.instructionPC 3738 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3738 _ (by rfl)
    _ = 4943 := by rw [csubPC3738]; rfl

@[simp] theorem csubPC3740 : Artifact.submissionArtifact.instructionPC 3740 = 4944 := by
  calc
    Artifact.submissionArtifact.instructionPC 3740 =
        Artifact.submissionArtifact.instructionPC 3739 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3739 _ (by rfl)
    _ = 4944 := by rw [csubPC3739]; rfl

@[simp] theorem csubPC3741 : Artifact.submissionArtifact.instructionPC 3741 = 4945 := by
  calc
    Artifact.submissionArtifact.instructionPC 3741 =
        Artifact.submissionArtifact.instructionPC 3740 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3740 _ (by rfl)
    _ = 4945 := by rw [csubPC3740]; rfl

@[simp] theorem csubPC3742 : Artifact.submissionArtifact.instructionPC 3742 = 4946 := by
  calc
    Artifact.submissionArtifact.instructionPC 3742 =
        Artifact.submissionArtifact.instructionPC 3741 + (YulEvmCompiler.Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3741 _ (by rfl)
    _ = 4946 := by rw [csubPC3741]; rfl

@[simp] theorem csubPC3743 : Artifact.submissionArtifact.instructionPC 3743 = 4947 := by
  calc
    Artifact.submissionArtifact.instructionPC 3743 =
        Artifact.submissionArtifact.instructionPC 3742 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3742 _ (by rfl)
    _ = 4947 := by rw [csubPC3742]; rfl

@[simp] theorem csubPC3744 : Artifact.submissionArtifact.instructionPC 3744 = 4948 := by
  calc
    Artifact.submissionArtifact.instructionPC 3744 =
        Artifact.submissionArtifact.instructionPC 3743 + (YulEvmCompiler.Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3743 _ (by rfl)
    _ = 4948 := by rw [csubPC3743]; rfl

@[simp] theorem csubPC3745 : Artifact.submissionArtifact.instructionPC 3745 = 4949 := by
  calc
    Artifact.submissionArtifact.instructionPC 3745 =
        Artifact.submissionArtifact.instructionPC 3744 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3744 _ (by rfl)
    _ = 4949 := by rw [csubPC3744]; rfl

@[simp] theorem csubPC3746 : Artifact.submissionArtifact.instructionPC 3746 = 4950 := by
  calc
    Artifact.submissionArtifact.instructionPC 3746 =
        Artifact.submissionArtifact.instructionPC 3745 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3745 _ (by rfl)
    _ = 4950 := by rw [csubPC3745]; rfl

@[simp] theorem csubPC3747 : Artifact.submissionArtifact.instructionPC 3747 = 4951 := by
  calc
    Artifact.submissionArtifact.instructionPC 3747 =
        Artifact.submissionArtifact.instructionPC 3746 + (YulEvmCompiler.Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3746 _ (by rfl)
    _ = 4951 := by rw [csubPC3746]; rfl

@[simp] theorem csubPC3748 : Artifact.submissionArtifact.instructionPC 3748 = 4952 := by
  calc
    Artifact.submissionArtifact.instructionPC 3748 =
        Artifact.submissionArtifact.instructionPC 3747 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3747 _ (by rfl)
    _ = 4952 := by rw [csubPC3747]; rfl

@[simp] theorem csubPC3749 : Artifact.submissionArtifact.instructionPC 3749 = 4953 := by
  calc
    Artifact.submissionArtifact.instructionPC 3749 =
        Artifact.submissionArtifact.instructionPC 3748 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3748 _ (by rfl)
    _ = 4953 := by rw [csubPC3748]; rfl

@[simp] theorem csubPC3750 : Artifact.submissionArtifact.instructionPC 3750 = 4954 := by
  calc
    Artifact.submissionArtifact.instructionPC 3750 =
        Artifact.submissionArtifact.instructionPC 3749 + (YulEvmCompiler.Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3749 _ (by rfl)
    _ = 4954 := by rw [csubPC3749]; rfl

@[simp] theorem csubPC3751 : Artifact.submissionArtifact.instructionPC 3751 = 4957 := by
  calc
    Artifact.submissionArtifact.instructionPC 3751 =
        Artifact.submissionArtifact.instructionPC 3750 + (YulEvmCompiler.Instr.push 2 1952).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3750 _ (by rfl)
    _ = 4957 := by rw [csubPC3750]; rfl

@[simp] theorem csubPC3752 : Artifact.submissionArtifact.instructionPC 3752 = 4958 := by
  calc
    Artifact.submissionArtifact.instructionPC 3752 =
        Artifact.submissionArtifact.instructionPC 3751 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3751 _ (by rfl)
    _ = 4958 := by rw [csubPC3751]; rfl

@[simp] theorem csubPC3753 : Artifact.submissionArtifact.instructionPC 3753 = 4961 := by
  calc
    Artifact.submissionArtifact.instructionPC 3753 =
        Artifact.submissionArtifact.instructionPC 3752 + (YulEvmCompiler.Instr.push 2 2240).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3752 _ (by rfl)
    _ = 4961 := by rw [csubPC3752]; rfl

@[simp] theorem csubPC3754 : Artifact.submissionArtifact.instructionPC 3754 = 4962 := by
  calc
    Artifact.submissionArtifact.instructionPC 3754 =
        Artifact.submissionArtifact.instructionPC 3753 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3753 _ (by rfl)
    _ = 4962 := by rw [csubPC3753]; rfl

@[simp] theorem csubPC3755 : Artifact.submissionArtifact.instructionPC 3755 = 4964 := by
  calc
    Artifact.submissionArtifact.instructionPC 3755 =
        Artifact.submissionArtifact.instructionPC 3754 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3754 _ (by rfl)
    _ = 4964 := by rw [csubPC3754]; rfl

@[simp] theorem csubPC3756 : Artifact.submissionArtifact.instructionPC 3756 = 4965 := by
  calc
    Artifact.submissionArtifact.instructionPC 3756 =
        Artifact.submissionArtifact.instructionPC 3755 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3755 _ (by rfl)
    _ = 4965 := by rw [csubPC3755]; rfl

@[simp] theorem csubPC3757 : Artifact.submissionArtifact.instructionPC 3757 = 4966 := by
  calc
    Artifact.submissionArtifact.instructionPC 3757 =
        Artifact.submissionArtifact.instructionPC 3756 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3756 _ (by rfl)
    _ = 4966 := by rw [csubPC3756]; rfl

@[simp] theorem csubPC3758 : Artifact.submissionArtifact.instructionPC 3758 = 4967 := by
  calc
    Artifact.submissionArtifact.instructionPC 3758 =
        Artifact.submissionArtifact.instructionPC 3757 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3757 _ (by rfl)
    _ = 4967 := by rw [csubPC3757]; rfl

@[simp] theorem csubPC3759 : Artifact.submissionArtifact.instructionPC 3759 = 4968 := by
  calc
    Artifact.submissionArtifact.instructionPC 3759 =
        Artifact.submissionArtifact.instructionPC 3758 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3758 _ (by rfl)
    _ = 4968 := by rw [csubPC3758]; rfl

@[simp] theorem csubPC3760 : Artifact.submissionArtifact.instructionPC 3760 = 4969 := by
  calc
    Artifact.submissionArtifact.instructionPC 3760 =
        Artifact.submissionArtifact.instructionPC 3759 + (YulEvmCompiler.Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3759 _ (by rfl)
    _ = 4969 := by rw [csubPC3759]; rfl

@[simp] theorem csubPC3761 : Artifact.submissionArtifact.instructionPC 3761 = 4970 := by
  calc
    Artifact.submissionArtifact.instructionPC 3761 =
        Artifact.submissionArtifact.instructionPC 3760 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3760 _ (by rfl)
    _ = 4970 := by rw [csubPC3760]; rfl

@[simp] theorem csubPC3762 : Artifact.submissionArtifact.instructionPC 3762 = 4971 := by
  calc
    Artifact.submissionArtifact.instructionPC 3762 =
        Artifact.submissionArtifact.instructionPC 3761 + (YulEvmCompiler.Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3761 _ (by rfl)
    _ = 4971 := by rw [csubPC3761]; rfl

@[simp] theorem csubPC3763 : Artifact.submissionArtifact.instructionPC 3763 = 4972 := by
  calc
    Artifact.submissionArtifact.instructionPC 3763 =
        Artifact.submissionArtifact.instructionPC 3762 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3762 _ (by rfl)
    _ = 4972 := by rw [csubPC3762]; rfl

@[simp] theorem csubPC3764 : Artifact.submissionArtifact.instructionPC 3764 = 4973 := by
  calc
    Artifact.submissionArtifact.instructionPC 3764 =
        Artifact.submissionArtifact.instructionPC 3763 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3763 _ (by rfl)
    _ = 4973 := by rw [csubPC3763]; rfl

@[simp] theorem csubPC3765 : Artifact.submissionArtifact.instructionPC 3765 = 4974 := by
  calc
    Artifact.submissionArtifact.instructionPC 3765 =
        Artifact.submissionArtifact.instructionPC 3764 + (YulEvmCompiler.Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3764 _ (by rfl)
    _ = 4974 := by rw [csubPC3764]; rfl

@[simp] theorem csubPC3766 : Artifact.submissionArtifact.instructionPC 3766 = 4975 := by
  calc
    Artifact.submissionArtifact.instructionPC 3766 =
        Artifact.submissionArtifact.instructionPC 3765 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3765 _ (by rfl)
    _ = 4975 := by rw [csubPC3765]; rfl

@[simp] theorem csubPC3767 : Artifact.submissionArtifact.instructionPC 3767 = 4976 := by
  calc
    Artifact.submissionArtifact.instructionPC 3767 =
        Artifact.submissionArtifact.instructionPC 3766 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3766 _ (by rfl)
    _ = 4976 := by rw [csubPC3766]; rfl

@[simp] theorem csubPC3768 : Artifact.submissionArtifact.instructionPC 3768 = 4977 := by
  calc
    Artifact.submissionArtifact.instructionPC 3768 =
        Artifact.submissionArtifact.instructionPC 3767 + (YulEvmCompiler.Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3767 _ (by rfl)
    _ = 4977 := by rw [csubPC3767]; rfl

@[simp] theorem csubPC3769 : Artifact.submissionArtifact.instructionPC 3769 = 4980 := by
  calc
    Artifact.submissionArtifact.instructionPC 3769 =
        Artifact.submissionArtifact.instructionPC 3768 + (YulEvmCompiler.Instr.push 2 1920).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3768 _ (by rfl)
    _ = 4980 := by rw [csubPC3768]; rfl

@[simp] theorem csubPC3770 : Artifact.submissionArtifact.instructionPC 3770 = 4981 := by
  calc
    Artifact.submissionArtifact.instructionPC 3770 =
        Artifact.submissionArtifact.instructionPC 3769 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3769 _ (by rfl)
    _ = 4981 := by rw [csubPC3769]; rfl

@[simp] theorem csubPC3771 : Artifact.submissionArtifact.instructionPC 3771 = 4984 := by
  calc
    Artifact.submissionArtifact.instructionPC 3771 =
        Artifact.submissionArtifact.instructionPC 3770 + (YulEvmCompiler.Instr.push 2 2208).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3770 _ (by rfl)
    _ = 4984 := by rw [csubPC3770]; rfl

@[simp] theorem csubPC3772 : Artifact.submissionArtifact.instructionPC 3772 = 4985 := by
  calc
    Artifact.submissionArtifact.instructionPC 3772 =
        Artifact.submissionArtifact.instructionPC 3771 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3771 _ (by rfl)
    _ = 4985 := by rw [csubPC3771]; rfl

@[simp] theorem csubPC3773 : Artifact.submissionArtifact.instructionPC 3773 = 4987 := by
  calc
    Artifact.submissionArtifact.instructionPC 3773 =
        Artifact.submissionArtifact.instructionPC 3772 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3772 _ (by rfl)
    _ = 4987 := by rw [csubPC3772]; rfl

@[simp] theorem csubPC3774 : Artifact.submissionArtifact.instructionPC 3774 = 4988 := by
  calc
    Artifact.submissionArtifact.instructionPC 3774 =
        Artifact.submissionArtifact.instructionPC 3773 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3773 _ (by rfl)
    _ = 4988 := by rw [csubPC3773]; rfl

@[simp] theorem csubPC3775 : Artifact.submissionArtifact.instructionPC 3775 = 4989 := by
  calc
    Artifact.submissionArtifact.instructionPC 3775 =
        Artifact.submissionArtifact.instructionPC 3774 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3774 _ (by rfl)
    _ = 4989 := by rw [csubPC3774]; rfl

@[simp] theorem csubPC3776 : Artifact.submissionArtifact.instructionPC 3776 = 4990 := by
  calc
    Artifact.submissionArtifact.instructionPC 3776 =
        Artifact.submissionArtifact.instructionPC 3775 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3775 _ (by rfl)
    _ = 4990 := by rw [csubPC3775]; rfl

@[simp] theorem csubPC3777 : Artifact.submissionArtifact.instructionPC 3777 = 4991 := by
  calc
    Artifact.submissionArtifact.instructionPC 3777 =
        Artifact.submissionArtifact.instructionPC 3776 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3776 _ (by rfl)
    _ = 4991 := by rw [csubPC3776]; rfl

@[simp] theorem csubPC3778 : Artifact.submissionArtifact.instructionPC 3778 = 4992 := by
  calc
    Artifact.submissionArtifact.instructionPC 3778 =
        Artifact.submissionArtifact.instructionPC 3777 + (YulEvmCompiler.Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3777 _ (by rfl)
    _ = 4992 := by rw [csubPC3777]; rfl

@[simp] theorem csubPC3779 : Artifact.submissionArtifact.instructionPC 3779 = 4993 := by
  calc
    Artifact.submissionArtifact.instructionPC 3779 =
        Artifact.submissionArtifact.instructionPC 3778 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3778 _ (by rfl)
    _ = 4993 := by rw [csubPC3778]; rfl

@[simp] theorem csubPC3780 : Artifact.submissionArtifact.instructionPC 3780 = 4994 := by
  calc
    Artifact.submissionArtifact.instructionPC 3780 =
        Artifact.submissionArtifact.instructionPC 3779 + (YulEvmCompiler.Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3779 _ (by rfl)
    _ = 4994 := by rw [csubPC3779]; rfl

@[simp] theorem csubPC3781 : Artifact.submissionArtifact.instructionPC 3781 = 4995 := by
  calc
    Artifact.submissionArtifact.instructionPC 3781 =
        Artifact.submissionArtifact.instructionPC 3780 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3780 _ (by rfl)
    _ = 4995 := by rw [csubPC3780]; rfl

@[simp] theorem csubPC3782 : Artifact.submissionArtifact.instructionPC 3782 = 4996 := by
  calc
    Artifact.submissionArtifact.instructionPC 3782 =
        Artifact.submissionArtifact.instructionPC 3781 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3781 _ (by rfl)
    _ = 4996 := by rw [csubPC3781]; rfl

@[simp] theorem csubPC3783 : Artifact.submissionArtifact.instructionPC 3783 = 4997 := by
  calc
    Artifact.submissionArtifact.instructionPC 3783 =
        Artifact.submissionArtifact.instructionPC 3782 + (YulEvmCompiler.Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3782 _ (by rfl)
    _ = 4997 := by rw [csubPC3782]; rfl

@[simp] theorem csubPC3784 : Artifact.submissionArtifact.instructionPC 3784 = 4998 := by
  calc
    Artifact.submissionArtifact.instructionPC 3784 =
        Artifact.submissionArtifact.instructionPC 3783 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3783 _ (by rfl)
    _ = 4998 := by rw [csubPC3783]; rfl

@[simp] theorem csubPC3785 : Artifact.submissionArtifact.instructionPC 3785 = 4999 := by
  calc
    Artifact.submissionArtifact.instructionPC 3785 =
        Artifact.submissionArtifact.instructionPC 3784 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3784 _ (by rfl)
    _ = 4999 := by rw [csubPC3784]; rfl

@[simp] theorem csubPC3786 : Artifact.submissionArtifact.instructionPC 3786 = 5000 := by
  calc
    Artifact.submissionArtifact.instructionPC 3786 =
        Artifact.submissionArtifact.instructionPC 3785 + (YulEvmCompiler.Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3785 _ (by rfl)
    _ = 5000 := by rw [csubPC3785]; rfl

@[simp] theorem csubPC3787 : Artifact.submissionArtifact.instructionPC 3787 = 5003 := by
  calc
    Artifact.submissionArtifact.instructionPC 3787 =
        Artifact.submissionArtifact.instructionPC 3786 + (YulEvmCompiler.Instr.push 2 1888).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3786 _ (by rfl)
    _ = 5003 := by rw [csubPC3786]; rfl

@[simp] theorem csubPC3788 : Artifact.submissionArtifact.instructionPC 3788 = 5004 := by
  calc
    Artifact.submissionArtifact.instructionPC 3788 =
        Artifact.submissionArtifact.instructionPC 3787 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3787 _ (by rfl)
    _ = 5004 := by rw [csubPC3787]; rfl

@[simp] theorem csubPC3789 : Artifact.submissionArtifact.instructionPC 3789 = 5005 := by
  calc
    Artifact.submissionArtifact.instructionPC 3789 =
        Artifact.submissionArtifact.instructionPC 3788 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3788 _ (by rfl)
    _ = 5005 := by rw [csubPC3788]; rfl

@[simp] theorem csubPC3790 : Artifact.submissionArtifact.instructionPC 3790 = 5008 := by
  calc
    Artifact.submissionArtifact.instructionPC 3790 =
        Artifact.submissionArtifact.instructionPC 3789 + (YulEvmCompiler.Instr.push 2 2176).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3789 _ (by rfl)
    _ = 5008 := by rw [csubPC3789]; rfl

@[simp] theorem csubPC3791 : Artifact.submissionArtifact.instructionPC 3791 = 5009 := by
  calc
    Artifact.submissionArtifact.instructionPC 3791 =
        Artifact.submissionArtifact.instructionPC 3790 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3790 _ (by rfl)
    _ = 5009 := by rw [csubPC3790]; rfl

@[simp] theorem csubPC3792 : Artifact.submissionArtifact.instructionPC 3792 = 5011 := by
  calc
    Artifact.submissionArtifact.instructionPC 3792 =
        Artifact.submissionArtifact.instructionPC 3791 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3791 _ (by rfl)
    _ = 5011 := by rw [csubPC3791]; rfl

@[simp] theorem csubPC3793 : Artifact.submissionArtifact.instructionPC 3793 = 5012 := by
  calc
    Artifact.submissionArtifact.instructionPC 3793 =
        Artifact.submissionArtifact.instructionPC 3792 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3792 _ (by rfl)
    _ = 5012 := by rw [csubPC3792]; rfl

@[simp] theorem csubPC3794 : Artifact.submissionArtifact.instructionPC 3794 = 5013 := by
  calc
    Artifact.submissionArtifact.instructionPC 3794 =
        Artifact.submissionArtifact.instructionPC 3793 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3793 _ (by rfl)
    _ = 5013 := by rw [csubPC3793]; rfl

@[simp] theorem csubPC3795 : Artifact.submissionArtifact.instructionPC 3795 = 5014 := by
  calc
    Artifact.submissionArtifact.instructionPC 3795 =
        Artifact.submissionArtifact.instructionPC 3794 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3794 _ (by rfl)
    _ = 5014 := by rw [csubPC3794]; rfl

@[simp] theorem csubPC3796 : Artifact.submissionArtifact.instructionPC 3796 = 5015 := by
  calc
    Artifact.submissionArtifact.instructionPC 3796 =
        Artifact.submissionArtifact.instructionPC 3795 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3795 _ (by rfl)
    _ = 5015 := by rw [csubPC3795]; rfl

@[simp] theorem csubPC3797 : Artifact.submissionArtifact.instructionPC 3797 = 5016 := by
  calc
    Artifact.submissionArtifact.instructionPC 3797 =
        Artifact.submissionArtifact.instructionPC 3796 + (YulEvmCompiler.Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3796 _ (by rfl)
    _ = 5016 := by rw [csubPC3796]; rfl

@[simp] theorem csubPC3798 : Artifact.submissionArtifact.instructionPC 3798 = 5017 := by
  calc
    Artifact.submissionArtifact.instructionPC 3798 =
        Artifact.submissionArtifact.instructionPC 3797 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3797 _ (by rfl)
    _ = 5017 := by rw [csubPC3797]; rfl

@[simp] theorem csubPC3799 : Artifact.submissionArtifact.instructionPC 3799 = 5018 := by
  calc
    Artifact.submissionArtifact.instructionPC 3799 =
        Artifact.submissionArtifact.instructionPC 3798 + (YulEvmCompiler.Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3798 _ (by rfl)
    _ = 5018 := by rw [csubPC3798]; rfl

@[simp] theorem csubPC3800 : Artifact.submissionArtifact.instructionPC 3800 = 5019 := by
  calc
    Artifact.submissionArtifact.instructionPC 3800 =
        Artifact.submissionArtifact.instructionPC 3799 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3799 _ (by rfl)
    _ = 5019 := by rw [csubPC3799]; rfl

@[simp] theorem csubPC3801 : Artifact.submissionArtifact.instructionPC 3801 = 5020 := by
  calc
    Artifact.submissionArtifact.instructionPC 3801 =
        Artifact.submissionArtifact.instructionPC 3800 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3800 _ (by rfl)
    _ = 5020 := by rw [csubPC3800]; rfl

@[simp] theorem csubPC3802 : Artifact.submissionArtifact.instructionPC 3802 = 5021 := by
  calc
    Artifact.submissionArtifact.instructionPC 3802 =
        Artifact.submissionArtifact.instructionPC 3801 + (YulEvmCompiler.Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3801 _ (by rfl)
    _ = 5021 := by rw [csubPC3801]; rfl

@[simp] theorem csubPC3803 : Artifact.submissionArtifact.instructionPC 3803 = 5022 := by
  calc
    Artifact.submissionArtifact.instructionPC 3803 =
        Artifact.submissionArtifact.instructionPC 3802 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3802 _ (by rfl)
    _ = 5022 := by rw [csubPC3802]; rfl

@[simp] theorem csubPC3804 : Artifact.submissionArtifact.instructionPC 3804 = 5023 := by
  calc
    Artifact.submissionArtifact.instructionPC 3804 =
        Artifact.submissionArtifact.instructionPC 3803 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3803 _ (by rfl)
    _ = 5023 := by rw [csubPC3803]; rfl

@[simp] theorem csubPC3805 : Artifact.submissionArtifact.instructionPC 3805 = 5024 := by
  calc
    Artifact.submissionArtifact.instructionPC 3805 =
        Artifact.submissionArtifact.instructionPC 3804 + (YulEvmCompiler.Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3804 _ (by rfl)
    _ = 5024 := by rw [csubPC3804]; rfl

@[simp] theorem csubPC3806 : Artifact.submissionArtifact.instructionPC 3806 = 5027 := by
  calc
    Artifact.submissionArtifact.instructionPC 3806 =
        Artifact.submissionArtifact.instructionPC 3805 + (YulEvmCompiler.Instr.push 2 1856).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3805 _ (by rfl)
    _ = 5027 := by rw [csubPC3805]; rfl

@[simp] theorem csubPC3807 : Artifact.submissionArtifact.instructionPC 3807 = 5028 := by
  calc
    Artifact.submissionArtifact.instructionPC 3807 =
        Artifact.submissionArtifact.instructionPC 3806 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3806 _ (by rfl)
    _ = 5028 := by rw [csubPC3806]; rfl

@[simp] theorem csubPC3808 : Artifact.submissionArtifact.instructionPC 3808 = 5031 := by
  calc
    Artifact.submissionArtifact.instructionPC 3808 =
        Artifact.submissionArtifact.instructionPC 3807 + (YulEvmCompiler.Instr.push 2 2144).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3807 _ (by rfl)
    _ = 5031 := by rw [csubPC3807]; rfl

@[simp] theorem csubPC3809 : Artifact.submissionArtifact.instructionPC 3809 = 5032 := by
  calc
    Artifact.submissionArtifact.instructionPC 3809 =
        Artifact.submissionArtifact.instructionPC 3808 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3808 _ (by rfl)
    _ = 5032 := by rw [csubPC3808]; rfl

@[simp] theorem csubPC3810 : Artifact.submissionArtifact.instructionPC 3810 = 5034 := by
  calc
    Artifact.submissionArtifact.instructionPC 3810 =
        Artifact.submissionArtifact.instructionPC 3809 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3809 _ (by rfl)
    _ = 5034 := by rw [csubPC3809]; rfl

@[simp] theorem csubPC3811 : Artifact.submissionArtifact.instructionPC 3811 = 5035 := by
  calc
    Artifact.submissionArtifact.instructionPC 3811 =
        Artifact.submissionArtifact.instructionPC 3810 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3810 _ (by rfl)
    _ = 5035 := by rw [csubPC3810]; rfl

@[simp] theorem csubPC3812 : Artifact.submissionArtifact.instructionPC 3812 = 5036 := by
  calc
    Artifact.submissionArtifact.instructionPC 3812 =
        Artifact.submissionArtifact.instructionPC 3811 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3811 _ (by rfl)
    _ = 5036 := by rw [csubPC3811]; rfl

@[simp] theorem csubPC3813 : Artifact.submissionArtifact.instructionPC 3813 = 5037 := by
  calc
    Artifact.submissionArtifact.instructionPC 3813 =
        Artifact.submissionArtifact.instructionPC 3812 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3812 _ (by rfl)
    _ = 5037 := by rw [csubPC3812]; rfl

@[simp] theorem csubPC3814 : Artifact.submissionArtifact.instructionPC 3814 = 5038 := by
  calc
    Artifact.submissionArtifact.instructionPC 3814 =
        Artifact.submissionArtifact.instructionPC 3813 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3813 _ (by rfl)
    _ = 5038 := by rw [csubPC3813]; rfl

@[simp] theorem csubPC3815 : Artifact.submissionArtifact.instructionPC 3815 = 5039 := by
  calc
    Artifact.submissionArtifact.instructionPC 3815 =
        Artifact.submissionArtifact.instructionPC 3814 + (YulEvmCompiler.Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3814 _ (by rfl)
    _ = 5039 := by rw [csubPC3814]; rfl

@[simp] theorem csubPC3816 : Artifact.submissionArtifact.instructionPC 3816 = 5040 := by
  calc
    Artifact.submissionArtifact.instructionPC 3816 =
        Artifact.submissionArtifact.instructionPC 3815 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3815 _ (by rfl)
    _ = 5040 := by rw [csubPC3815]; rfl

@[simp] theorem csubPC3817 : Artifact.submissionArtifact.instructionPC 3817 = 5041 := by
  calc
    Artifact.submissionArtifact.instructionPC 3817 =
        Artifact.submissionArtifact.instructionPC 3816 + (YulEvmCompiler.Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3816 _ (by rfl)
    _ = 5041 := by rw [csubPC3816]; rfl

@[simp] theorem csubPC3818 : Artifact.submissionArtifact.instructionPC 3818 = 5042 := by
  calc
    Artifact.submissionArtifact.instructionPC 3818 =
        Artifact.submissionArtifact.instructionPC 3817 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3817 _ (by rfl)
    _ = 5042 := by rw [csubPC3817]; rfl

@[simp] theorem csubPC3819 : Artifact.submissionArtifact.instructionPC 3819 = 5043 := by
  calc
    Artifact.submissionArtifact.instructionPC 3819 =
        Artifact.submissionArtifact.instructionPC 3818 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3818 _ (by rfl)
    _ = 5043 := by rw [csubPC3818]; rfl

@[simp] theorem csubPC3820 : Artifact.submissionArtifact.instructionPC 3820 = 5044 := by
  calc
    Artifact.submissionArtifact.instructionPC 3820 =
        Artifact.submissionArtifact.instructionPC 3819 + (YulEvmCompiler.Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3819 _ (by rfl)
    _ = 5044 := by rw [csubPC3819]; rfl

@[simp] theorem csubPC3821 : Artifact.submissionArtifact.instructionPC 3821 = 5045 := by
  calc
    Artifact.submissionArtifact.instructionPC 3821 =
        Artifact.submissionArtifact.instructionPC 3820 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3820 _ (by rfl)
    _ = 5045 := by rw [csubPC3820]; rfl

@[simp] theorem csubPC3822 : Artifact.submissionArtifact.instructionPC 3822 = 5046 := by
  calc
    Artifact.submissionArtifact.instructionPC 3822 =
        Artifact.submissionArtifact.instructionPC 3821 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3821 _ (by rfl)
    _ = 5046 := by rw [csubPC3821]; rfl

@[simp] theorem csubPC3823 : Artifact.submissionArtifact.instructionPC 3823 = 5047 := by
  calc
    Artifact.submissionArtifact.instructionPC 3823 =
        Artifact.submissionArtifact.instructionPC 3822 + (YulEvmCompiler.Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3822 _ (by rfl)
    _ = 5047 := by rw [csubPC3822]; rfl

@[simp] theorem csubPC3824 : Artifact.submissionArtifact.instructionPC 3824 = 5050 := by
  calc
    Artifact.submissionArtifact.instructionPC 3824 =
        Artifact.submissionArtifact.instructionPC 3823 + (YulEvmCompiler.Instr.push 2 1824).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3823 _ (by rfl)
    _ = 5050 := by rw [csubPC3823]; rfl

@[simp] theorem csubPC3825 : Artifact.submissionArtifact.instructionPC 3825 = 5051 := by
  calc
    Artifact.submissionArtifact.instructionPC 3825 =
        Artifact.submissionArtifact.instructionPC 3824 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3824 _ (by rfl)
    _ = 5051 := by rw [csubPC3824]; rfl

@[simp] theorem csubPC3826 : Artifact.submissionArtifact.instructionPC 3826 = 5054 := by
  calc
    Artifact.submissionArtifact.instructionPC 3826 =
        Artifact.submissionArtifact.instructionPC 3825 + (YulEvmCompiler.Instr.push 2 2112).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3825 _ (by rfl)
    _ = 5054 := by rw [csubPC3825]; rfl

@[simp] theorem csubPC3827 : Artifact.submissionArtifact.instructionPC 3827 = 5055 := by
  calc
    Artifact.submissionArtifact.instructionPC 3827 =
        Artifact.submissionArtifact.instructionPC 3826 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3826 _ (by rfl)
    _ = 5055 := by rw [csubPC3826]; rfl

@[simp] theorem csubPC3828 : Artifact.submissionArtifact.instructionPC 3828 = 5056 := by
  calc
    Artifact.submissionArtifact.instructionPC 3828 =
        Artifact.submissionArtifact.instructionPC 3827 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3827 _ (by rfl)
    _ = 5056 := by rw [csubPC3827]; rfl

@[simp] theorem csubPC3829 : Artifact.submissionArtifact.instructionPC 3829 = 5057 := by
  calc
    Artifact.submissionArtifact.instructionPC 3829 =
        Artifact.submissionArtifact.instructionPC 3828 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3828 _ (by rfl)
    _ = 5057 := by rw [csubPC3828]; rfl

@[simp] theorem csubPC3830 : Artifact.submissionArtifact.instructionPC 3830 = 5058 := by
  calc
    Artifact.submissionArtifact.instructionPC 3830 =
        Artifact.submissionArtifact.instructionPC 3829 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3829 _ (by rfl)
    _ = 5058 := by rw [csubPC3829]; rfl

@[simp] theorem csubPC3831 : Artifact.submissionArtifact.instructionPC 3831 = 5059 := by
  calc
    Artifact.submissionArtifact.instructionPC 3831 =
        Artifact.submissionArtifact.instructionPC 3830 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3830 _ (by rfl)
    _ = 5059 := by rw [csubPC3830]; rfl

@[simp] theorem csubPC3832 : Artifact.submissionArtifact.instructionPC 3832 = 5060 := by
  calc
    Artifact.submissionArtifact.instructionPC 3832 =
        Artifact.submissionArtifact.instructionPC 3831 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3831 _ (by rfl)
    _ = 5060 := by rw [csubPC3831]; rfl

@[simp] theorem csubPC3833 : Artifact.submissionArtifact.instructionPC 3833 = 5061 := by
  calc
    Artifact.submissionArtifact.instructionPC 3833 =
        Artifact.submissionArtifact.instructionPC 3832 + (YulEvmCompiler.Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3832 _ (by rfl)
    _ = 5061 := by rw [csubPC3832]; rfl

@[simp] theorem csubPC3834 : Artifact.submissionArtifact.instructionPC 3834 = 5062 := by
  calc
    Artifact.submissionArtifact.instructionPC 3834 =
        Artifact.submissionArtifact.instructionPC 3833 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3833 _ (by rfl)
    _ = 5062 := by rw [csubPC3833]; rfl

@[simp] theorem csubPC3835 : Artifact.submissionArtifact.instructionPC 3835 = 5063 := by
  calc
    Artifact.submissionArtifact.instructionPC 3835 =
        Artifact.submissionArtifact.instructionPC 3834 + (YulEvmCompiler.Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3834 _ (by rfl)
    _ = 5063 := by rw [csubPC3834]; rfl

@[simp] theorem csubPC3836 : Artifact.submissionArtifact.instructionPC 3836 = 5064 := by
  calc
    Artifact.submissionArtifact.instructionPC 3836 =
        Artifact.submissionArtifact.instructionPC 3835 + (YulEvmCompiler.Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3835 _ (by rfl)
    _ = 5064 := by rw [csubPC3835]; rfl

@[simp] theorem csubPC3837 : Artifact.submissionArtifact.instructionPC 3837 = 5065 := by
  calc
    Artifact.submissionArtifact.instructionPC 3837 =
        Artifact.submissionArtifact.instructionPC 3836 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3836 _ (by rfl)
    _ = 5065 := by rw [csubPC3836]; rfl

@[simp] theorem csubPC3838 : Artifact.submissionArtifact.instructionPC 3838 = 5066 := by
  calc
    Artifact.submissionArtifact.instructionPC 3838 =
        Artifact.submissionArtifact.instructionPC 3837 + (YulEvmCompiler.Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3837 _ (by rfl)
    _ = 5066 := by rw [csubPC3837]; rfl

@[simp] theorem csubPC3839 : Artifact.submissionArtifact.instructionPC 3839 = 5067 := by
  calc
    Artifact.submissionArtifact.instructionPC 3839 =
        Artifact.submissionArtifact.instructionPC 3838 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3838 _ (by rfl)
    _ = 5067 := by rw [csubPC3838]; rfl

@[simp] theorem csubPC3840 : Artifact.submissionArtifact.instructionPC 3840 = 5068 := by
  calc
    Artifact.submissionArtifact.instructionPC 3840 =
        Artifact.submissionArtifact.instructionPC 3839 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3839 _ (by rfl)
    _ = 5068 := by rw [csubPC3839]; rfl

@[simp] theorem csubPC3841 : Artifact.submissionArtifact.instructionPC 3841 = 5069 := by
  calc
    Artifact.submissionArtifact.instructionPC 3841 =
        Artifact.submissionArtifact.instructionPC 3840 + (YulEvmCompiler.Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3840 _ (by rfl)
    _ = 5069 := by rw [csubPC3840]; rfl

@[simp] theorem csubPC3842 : Artifact.submissionArtifact.instructionPC 3842 = 5072 := by
  calc
    Artifact.submissionArtifact.instructionPC 3842 =
        Artifact.submissionArtifact.instructionPC 3841 + (YulEvmCompiler.Instr.push 2 1792).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3841 _ (by rfl)
    _ = 5072 := by rw [csubPC3841]; rfl

@[simp] theorem csubPC3843 : Artifact.submissionArtifact.instructionPC 3843 = 5073 := by
  calc
    Artifact.submissionArtifact.instructionPC 3843 =
        Artifact.submissionArtifact.instructionPC 3842 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3842 _ (by rfl)
    _ = 5073 := by rw [csubPC3842]; rfl

@[simp] theorem csubPC3844 : Artifact.submissionArtifact.instructionPC 3844 = 5074 := by
  calc
    Artifact.submissionArtifact.instructionPC 3844 =
        Artifact.submissionArtifact.instructionPC 3843 + (YulEvmCompiler.Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3843 _ (by rfl)
    _ = 5074 := by rw [csubPC3843]; rfl

@[simp] theorem csubPC3845 : Artifact.submissionArtifact.instructionPC 3845 = 5077 := by
  calc
    Artifact.submissionArtifact.instructionPC 3845 =
        Artifact.submissionArtifact.instructionPC 3844 + (YulEvmCompiler.Instr.push 2 2080).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3844 _ (by rfl)
    _ = 5077 := by rw [csubPC3844]; rfl

@[simp] theorem csubPC3846 : Artifact.submissionArtifact.instructionPC 3846 = 5078 := by
  calc
    Artifact.submissionArtifact.instructionPC 3846 =
        Artifact.submissionArtifact.instructionPC 3845 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3845 _ (by rfl)
    _ = 5078 := by rw [csubPC3845]; rfl

@[simp] theorem csubPC3847 : Artifact.submissionArtifact.instructionPC 3847 = 5079 := by
  calc
    Artifact.submissionArtifact.instructionPC 3847 =
        Artifact.submissionArtifact.instructionPC 3846 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3846 _ (by rfl)
    _ = 5079 := by rw [csubPC3846]; rfl

@[simp] theorem csubPC3848 : Artifact.submissionArtifact.instructionPC 3848 = 5082 := by
  calc
    Artifact.submissionArtifact.instructionPC 3848 =
        Artifact.submissionArtifact.instructionPC 3847 + (YulEvmCompiler.Instr.push 2 319).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3847 _ (by rfl)
    _ = 5082 := by rw [csubPC3847]; rfl

@[simp] theorem csubPC3849 : Artifact.submissionArtifact.instructionPC 3849 = 5083 := by
  calc
    Artifact.submissionArtifact.instructionPC 3849 =
        Artifact.submissionArtifact.instructionPC 3848 + (YulEvmCompiler.Instr.op .NOT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3848 _ (by rfl)
    _ = 5083 := by rw [csubPC3848]; rfl

@[simp] theorem csubPC3850 : Artifact.submissionArtifact.instructionPC 3850 = 5086 := by
  calc
    Artifact.submissionArtifact.instructionPC 3850 =
        Artifact.submissionArtifact.instructionPC 3849 + (YulEvmCompiler.Instr.push 2 5098).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3849 _ (by rfl)
    _ = 5086 := by rw [csubPC3849]; rfl

@[simp] theorem csubPC3858 : Artifact.submissionArtifact.instructionPC 3858 = 5098 := by rfl

@[simp] theorem csubPC3859 : Artifact.submissionArtifact.instructionPC 3859 = 5099 := by
  calc
    Artifact.submissionArtifact.instructionPC 3859 =
        Artifact.submissionArtifact.instructionPC 3858 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3858 _ (by rfl)
    _ = 5099 := by rw [csubPC3858]; rfl

@[simp] theorem csubPC3860 : Artifact.submissionArtifact.instructionPC 3860 = 5100 := by
  calc
    Artifact.submissionArtifact.instructionPC 3860 =
        Artifact.submissionArtifact.instructionPC 3859 + (YulEvmCompiler.Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3859 _ (by rfl)
    _ = 5100 := by rw [csubPC3859]; rfl

@[simp] theorem csubPC3861 : Artifact.submissionArtifact.instructionPC 3861 = 5103 := by
  calc
    Artifact.submissionArtifact.instructionPC 3861 =
        Artifact.submissionArtifact.instructionPC 3860 + (YulEvmCompiler.Instr.push 2 2112).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3860 _ (by rfl)
    _ = 5103 := by rw [csubPC3860]; rfl

@[simp] theorem csubPC3862 : Artifact.submissionArtifact.instructionPC 3862 = 5104 := by
  calc
    Artifact.submissionArtifact.instructionPC 3862 =
        Artifact.submissionArtifact.instructionPC 3861 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3861 _ (by rfl)
    _ = 5104 := by rw [csubPC3861]; rfl

@[simp] theorem csubPC3863 : Artifact.submissionArtifact.instructionPC 3863 = 5107 := by
  calc
    Artifact.submissionArtifact.instructionPC 3863 =
        Artifact.submissionArtifact.instructionPC 3862 + (YulEvmCompiler.Instr.push 2 2784).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3862 _ (by rfl)
    _ = 5107 := by rw [csubPC3862]; rfl

@[simp] theorem csubPC3864 : Artifact.submissionArtifact.instructionPC 3864 = 5108 := by
  calc
    Artifact.submissionArtifact.instructionPC 3864 =
        Artifact.submissionArtifact.instructionPC 3863 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3863 _ (by rfl)
    _ = 5108 := by rw [csubPC3863]; rfl

@[simp] theorem csubPC3865 : Artifact.submissionArtifact.instructionPC 3865 = 5109 := by
  calc
    Artifact.submissionArtifact.instructionPC 3865 =
        Artifact.submissionArtifact.instructionPC 3864 + (YulEvmCompiler.Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3864 _ (by rfl)
    _ = 5109 := by rw [csubPC3864]; rfl

@[simp] theorem csubPC3866 : Artifact.submissionArtifact.instructionPC 3866 = 5110 := by
  calc
    Artifact.submissionArtifact.instructionPC 3866 =
        Artifact.submissionArtifact.instructionPC 3865 + (YulEvmCompiler.Instr.op .MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3865 _ (by rfl)
    _ = 5110 := by rw [csubPC3865]; rfl

@[simp] theorem csubJump4689 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4689 = true := by
  simpa only [Artifact.instructionPC, csubPC3576] using Artifact.isValidJumpDest_index 3576 (by rfl)

@[simp] theorem csubJump4895 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4895 = true := by
  simpa only [Artifact.instructionPC, csubPC3704] using Artifact.isValidJumpDest_index 3704 (by rfl)

@[simp] theorem csubJump5004 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5004 = true := by
  simpa only [Artifact.instructionPC, csubPC3788] using Artifact.isValidJumpDest_index 3788 (by rfl)

@[simp] theorem csubJump5098 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5098 = true := by
  simpa only [Artifact.instructionPC, csubPC3858] using Artifact.isValidJumpDest_index 3858 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
