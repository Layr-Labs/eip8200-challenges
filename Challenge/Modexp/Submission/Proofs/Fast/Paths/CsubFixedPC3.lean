import Challenge.Modexp.Submission.Proofs.Fast.Paths.CsubFixedPC2
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
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

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3548 = 4682 := by
  calc
    Artifact.submissionArtifact.instructionPC 3548 =
        Artifact.submissionArtifact.instructionPC 3547 + ((.op (.Swap ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3547 (.op (.Swap ⟨2, by decide⟩)) (by rfl)
    _ = 4682 := by rw [fixedPC3883]; rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3549 = 4683 := by
  calc
    Artifact.submissionArtifact.instructionPC 3549 =
        Artifact.submissionArtifact.instructionPC 3548 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3548 (.op .GT) (by rfl)
    _ = 4683 := by rw [fixedPC3884]; rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3550 = 4684 := by
  calc
    Artifact.submissionArtifact.instructionPC 3550 =
        Artifact.submissionArtifact.instructionPC 3549 + ((.op .OR) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3549 (.op .OR) (by rfl)
    _ = 4684 := by rw [fixedPC3885]; rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3551 = 4685 := by
  calc
    Artifact.submissionArtifact.instructionPC 3551 =
        Artifact.submissionArtifact.instructionPC 3550 + ((.op (.Swap ⟨0, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3550 (.op (.Swap ⟨0, by decide⟩)) (by rfl)
    _ = 4685 := by rw [fixedPC3886]; rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3552 = 4688 := by
  calc
    Artifact.submissionArtifact.instructionPC 3552 =
        Artifact.submissionArtifact.instructionPC 3551 + ((.push 2 1888) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3551 (.push 2 1888) (by rfl)
    _ = 4688 := by rw [fixedPC3887]; rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3553 = 4689 := by
  calc
    Artifact.submissionArtifact.instructionPC 3553 =
        Artifact.submissionArtifact.instructionPC 3552 + ((.op .MSTORE) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3552 (.op .MSTORE) (by rfl)
    _ = 4689 := by rw [fixedPC3888]; rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4689 = true := by
  simpa only [Artifact.instructionPC, fixedPC3889] using Artifact.isValidJumpDest_index 3553 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3554 = 4690 := by
  calc
    Artifact.submissionArtifact.instructionPC 3554 =
        Artifact.submissionArtifact.instructionPC 3553 + ((.op .JUMPDEST) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3553 (.op .JUMPDEST) (by rfl)
    _ = 4690 := by rw [fixedPC3889]; rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3555 = 4693 := by
  calc
    Artifact.submissionArtifact.instructionPC 3555 =
        Artifact.submissionArtifact.instructionPC 3554 + ((.push 2 2176) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3554 (.push 2 2176) (by rfl)
    _ = 4693 := by rw [fixedPC3890]; rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3556 = 4694 := by
  calc
    Artifact.submissionArtifact.instructionPC 3556 =
        Artifact.submissionArtifact.instructionPC 3555 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3555 (.op .MLOAD) (by rfl)
    _ = 4694 := by rw [fixedPC3891]; rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3557 = 4696 := by
  calc
    Artifact.submissionArtifact.instructionPC 3557 =
        Artifact.submissionArtifact.instructionPC 3556 + ((.push 1 64) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3556 (.push 1 64) (by rfl)
    _ = 4696 := by rw [fixedPC3892]; rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3558 = 4697 := by
  calc
    Artifact.submissionArtifact.instructionPC 3558 =
        Artifact.submissionArtifact.instructionPC 3557 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3557 (.op .MLOAD) (by rfl)
    _ = 4697 := by rw [fixedPC3893]; rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3559 = 4698 := by
  calc
    Artifact.submissionArtifact.instructionPC 3559 =
        Artifact.submissionArtifact.instructionPC 3558 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3558 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4698 := by rw [fixedPC3894]; rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3560 = 4699 := by
  calc
    Artifact.submissionArtifact.instructionPC 3560 =
        Artifact.submissionArtifact.instructionPC 3559 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3559 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4699 := by rw [fixedPC3895]; rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3561 = 4700 := by
  calc
    Artifact.submissionArtifact.instructionPC 3561 =
        Artifact.submissionArtifact.instructionPC 3560 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3560 (.op .GT) (by rfl)
    _ = 4700 := by rw [fixedPC3896]; rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3562 = 4701 := by
  calc
    Artifact.submissionArtifact.instructionPC 3562 =
        Artifact.submissionArtifact.instructionPC 3561 + ((.op (.Swap ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3561 (.op (.Swap ⟨1, by decide⟩)) (by rfl)
    _ = 4701 := by rw [fixedPC3897]; rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3563 = 4702 := by
  calc
    Artifact.submissionArtifact.instructionPC 3563 =
        Artifact.submissionArtifact.instructionPC 3562 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3562 (.op .SUB) (by rfl)
    _ = 4702 := by rw [fixedPC3898]; rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3564 = 4703 := by
  calc
    Artifact.submissionArtifact.instructionPC 3564 =
        Artifact.submissionArtifact.instructionPC 3563 + ((.op (.Dup ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3563 (.op (.Dup ⟨2, by decide⟩)) (by rfl)
    _ = 4703 := by rw [fixedPC3899]; rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3565 = 4704 := by
  calc
    Artifact.submissionArtifact.instructionPC 3565 =
        Artifact.submissionArtifact.instructionPC 3564 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3564 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4704 := by rw [fixedPC3900]; rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3566 = 4705 := by
  calc
    Artifact.submissionArtifact.instructionPC 3566 =
        Artifact.submissionArtifact.instructionPC 3565 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3565 (.op .SUB) (by rfl)
    _ = 4705 := by rw [fixedPC3901]; rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3567 = 4706 := by
  calc
    Artifact.submissionArtifact.instructionPC 3567 =
        Artifact.submissionArtifact.instructionPC 3566 + ((.op (.Swap ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3566 (.op (.Swap ⟨2, by decide⟩)) (by rfl)
    _ = 4706 := by rw [fixedPC3902]; rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3568 = 4707 := by
  calc
    Artifact.submissionArtifact.instructionPC 3568 =
        Artifact.submissionArtifact.instructionPC 3567 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3567 (.op .GT) (by rfl)
    _ = 4707 := by rw [fixedPC3903]; rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3569 = 4708 := by
  calc
    Artifact.submissionArtifact.instructionPC 3569 =
        Artifact.submissionArtifact.instructionPC 3568 + ((.op .OR) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3568 (.op .OR) (by rfl)
    _ = 4708 := by rw [fixedPC3904]; rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3570 = 4709 := by
  calc
    Artifact.submissionArtifact.instructionPC 3570 =
        Artifact.submissionArtifact.instructionPC 3569 + ((.op (.Swap ⟨0, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3569 (.op (.Swap ⟨0, by decide⟩)) (by rfl)
    _ = 4709 := by rw [fixedPC3905]; rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3571 = 4712 := by
  calc
    Artifact.submissionArtifact.instructionPC 3571 =
        Artifact.submissionArtifact.instructionPC 3570 + ((.push 2 1856) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3570 (.push 2 1856) (by rfl)
    _ = 4712 := by rw [fixedPC3906]; rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3572 = 4713 := by
  calc
    Artifact.submissionArtifact.instructionPC 3572 =
        Artifact.submissionArtifact.instructionPC 3571 + ((.op .MSTORE) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3571 (.op .MSTORE) (by rfl)
    _ = 4713 := by rw [fixedPC3907]; rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3573 = 4716 := by
  calc
    Artifact.submissionArtifact.instructionPC 3573 =
        Artifact.submissionArtifact.instructionPC 3572 + ((.push 2 2144) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3572 (.push 2 2144) (by rfl)
    _ = 4716 := by rw [fixedPC3908]; rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3574 = 4717 := by
  calc
    Artifact.submissionArtifact.instructionPC 3574 =
        Artifact.submissionArtifact.instructionPC 3573 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3573 (.op .MLOAD) (by rfl)
    _ = 4717 := by rw [fixedPC3909]; rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3575 = 4719 := by
  calc
    Artifact.submissionArtifact.instructionPC 3575 =
        Artifact.submissionArtifact.instructionPC 3574 + ((.push 1 32) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3574 (.push 1 32) (by rfl)
    _ = 4719 := by rw [fixedPC3910]; rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3576 = 4720 := by
  calc
    Artifact.submissionArtifact.instructionPC 3576 =
        Artifact.submissionArtifact.instructionPC 3575 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3575 (.op .MLOAD) (by rfl)
    _ = 4720 := by rw [fixedPC3911]; rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3577 = 4721 := by
  calc
    Artifact.submissionArtifact.instructionPC 3577 =
        Artifact.submissionArtifact.instructionPC 3576 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3576 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4721 := by rw [fixedPC3912]; rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3578 = 4722 := by
  calc
    Artifact.submissionArtifact.instructionPC 3578 =
        Artifact.submissionArtifact.instructionPC 3577 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3577 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4722 := by rw [fixedPC3913]; rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3579 = 4723 := by
  calc
    Artifact.submissionArtifact.instructionPC 3579 =
        Artifact.submissionArtifact.instructionPC 3578 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3578 (.op .GT) (by rfl)
    _ = 4723 := by rw [fixedPC3914]; rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3580 = 4724 := by
  calc
    Artifact.submissionArtifact.instructionPC 3580 =
        Artifact.submissionArtifact.instructionPC 3579 + ((.op (.Swap ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3579 (.op (.Swap ⟨1, by decide⟩)) (by rfl)
    _ = 4724 := by rw [fixedPC3915]; rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3581 = 4725 := by
  calc
    Artifact.submissionArtifact.instructionPC 3581 =
        Artifact.submissionArtifact.instructionPC 3580 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3580 (.op .SUB) (by rfl)
    _ = 4725 := by rw [fixedPC3916]; rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3582 = 4726 := by
  calc
    Artifact.submissionArtifact.instructionPC 3582 =
        Artifact.submissionArtifact.instructionPC 3581 + ((.op (.Dup ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3581 (.op (.Dup ⟨2, by decide⟩)) (by rfl)
    _ = 4726 := by rw [fixedPC3917]; rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3583 = 4727 := by
  calc
    Artifact.submissionArtifact.instructionPC 3583 =
        Artifact.submissionArtifact.instructionPC 3582 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3582 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4727 := by rw [fixedPC3918]; rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3584 = 4728 := by
  calc
    Artifact.submissionArtifact.instructionPC 3584 =
        Artifact.submissionArtifact.instructionPC 3583 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3583 (.op .SUB) (by rfl)
    _ = 4728 := by rw [fixedPC3919]; rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3585 = 4729 := by
  calc
    Artifact.submissionArtifact.instructionPC 3585 =
        Artifact.submissionArtifact.instructionPC 3584 + ((.op (.Swap ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3584 (.op (.Swap ⟨2, by decide⟩)) (by rfl)
    _ = 4729 := by rw [fixedPC3920]; rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3586 = 4730 := by
  calc
    Artifact.submissionArtifact.instructionPC 3586 =
        Artifact.submissionArtifact.instructionPC 3585 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3585 (.op .GT) (by rfl)
    _ = 4730 := by rw [fixedPC3921]; rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3587 = 4731 := by
  calc
    Artifact.submissionArtifact.instructionPC 3587 =
        Artifact.submissionArtifact.instructionPC 3586 + ((.op .OR) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3586 (.op .OR) (by rfl)
    _ = 4731 := by rw [fixedPC3922]; rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3588 = 4732 := by
  calc
    Artifact.submissionArtifact.instructionPC 3588 =
        Artifact.submissionArtifact.instructionPC 3587 + ((.op (.Swap ⟨0, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3587 (.op (.Swap ⟨0, by decide⟩)) (by rfl)
    _ = 4732 := by rw [fixedPC3923]; rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3589 = 4735 := by
  calc
    Artifact.submissionArtifact.instructionPC 3589 =
        Artifact.submissionArtifact.instructionPC 3588 + ((.push 2 1824) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3588 (.push 2 1824) (by rfl)
    _ = 4735 := by rw [fixedPC3924]; rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3590 = 4736 := by
  calc
    Artifact.submissionArtifact.instructionPC 3590 =
        Artifact.submissionArtifact.instructionPC 3589 + ((.op .MSTORE) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3589 (.op .MSTORE) (by rfl)
    _ = 4736 := by rw [fixedPC3925]; rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3591 = 4739 := by
  calc
    Artifact.submissionArtifact.instructionPC 3591 =
        Artifact.submissionArtifact.instructionPC 3590 + ((.push 2 2112) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3590 (.push 2 2112) (by rfl)
    _ = 4739 := by rw [fixedPC3926]; rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3592 = 4740 := by
  calc
    Artifact.submissionArtifact.instructionPC 3592 =
        Artifact.submissionArtifact.instructionPC 3591 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3591 (.op .MLOAD) (by rfl)
    _ = 4740 := by rw [fixedPC3927]; rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3593 = 4741 := by
  calc
    Artifact.submissionArtifact.instructionPC 3593 =
        Artifact.submissionArtifact.instructionPC 3592 + ((.push 0 0) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3592 (.push 0 0) (by rfl)
    _ = 4741 := by rw [fixedPC3928]; rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3594 = 4742 := by
  calc
    Artifact.submissionArtifact.instructionPC 3594 =
        Artifact.submissionArtifact.instructionPC 3593 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3593 (.op .MLOAD) (by rfl)
    _ = 4742 := by rw [fixedPC3929]; rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3595 = 4743 := by
  calc
    Artifact.submissionArtifact.instructionPC 3595 =
        Artifact.submissionArtifact.instructionPC 3594 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3594 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4743 := by rw [fixedPC3930]; rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3596 = 4744 := by
  calc
    Artifact.submissionArtifact.instructionPC 3596 =
        Artifact.submissionArtifact.instructionPC 3595 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3595 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4744 := by rw [fixedPC3931]; rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3597 = 4745 := by
  calc
    Artifact.submissionArtifact.instructionPC 3597 =
        Artifact.submissionArtifact.instructionPC 3596 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3596 (.op .GT) (by rfl)
    _ = 4745 := by rw [fixedPC3932]; rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3598 = 4746 := by
  calc
    Artifact.submissionArtifact.instructionPC 3598 =
        Artifact.submissionArtifact.instructionPC 3597 + ((.op (.Swap ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3597 (.op (.Swap ⟨1, by decide⟩)) (by rfl)
    _ = 4746 := by rw [fixedPC3933]; rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3599 = 4747 := by
  calc
    Artifact.submissionArtifact.instructionPC 3599 =
        Artifact.submissionArtifact.instructionPC 3598 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3598 (.op .SUB) (by rfl)
    _ = 4747 := by rw [fixedPC3934]; rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3600 = 4748 := by
  calc
    Artifact.submissionArtifact.instructionPC 3600 =
        Artifact.submissionArtifact.instructionPC 3599 + ((.op (.Dup ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3599 (.op (.Dup ⟨2, by decide⟩)) (by rfl)
    _ = 4748 := by rw [fixedPC3935]; rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3601 = 4749 := by
  calc
    Artifact.submissionArtifact.instructionPC 3601 =
        Artifact.submissionArtifact.instructionPC 3600 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3600 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4749 := by rw [fixedPC3936]; rfl


end Challenge.Modexp.Submission.Proofs.Fast
