import Challenge.Modexp.Submission.Proofs.Fast.Paths.CsubFixedPC1
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

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3493 = 4612 := by
  calc
    Artifact.submissionArtifact.instructionPC 3493 =
        Artifact.submissionArtifact.instructionPC 3492 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3492 (.op .SUB) (by rfl)
    _ = 4612 := by rw [fixedPC3827]; rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3494 = 4613 := by
  calc
    Artifact.submissionArtifact.instructionPC 3494 =
        Artifact.submissionArtifact.instructionPC 3493 + ((.op (.Swap ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3493 (.op (.Swap ⟨2, by decide⟩)) (by rfl)
    _ = 4613 := by rw [fixedPC3828]; rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3495 = 4614 := by
  calc
    Artifact.submissionArtifact.instructionPC 3495 =
        Artifact.submissionArtifact.instructionPC 3494 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3494 (.op .GT) (by rfl)
    _ = 4614 := by rw [fixedPC3829]; rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3496 = 4615 := by
  calc
    Artifact.submissionArtifact.instructionPC 3496 =
        Artifact.submissionArtifact.instructionPC 3495 + ((.op .OR) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3495 (.op .OR) (by rfl)
    _ = 4615 := by rw [fixedPC3830]; rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3497 = 4616 := by
  calc
    Artifact.submissionArtifact.instructionPC 3497 =
        Artifact.submissionArtifact.instructionPC 3496 + ((.op (.Swap ⟨0, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3496 (.op (.Swap ⟨0, by decide⟩)) (by rfl)
    _ = 4616 := by rw [fixedPC3831]; rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3498 = 4619 := by
  calc
    Artifact.submissionArtifact.instructionPC 3498 =
        Artifact.submissionArtifact.instructionPC 3497 + ((.push 2 1984) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3497 (.push 2 1984) (by rfl)
    _ = 4619 := by rw [fixedPC3832]; rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3499 = 4620 := by
  calc
    Artifact.submissionArtifact.instructionPC 3499 =
        Artifact.submissionArtifact.instructionPC 3498 + ((.op .MSTORE) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3498 (.op .MSTORE) (by rfl)
    _ = 4620 := by rw [fixedPC3833]; rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3500 = 4623 := by
  calc
    Artifact.submissionArtifact.instructionPC 3500 =
        Artifact.submissionArtifact.instructionPC 3499 + ((.push 2 2272) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3499 (.push 2 2272) (by rfl)
    _ = 4623 := by rw [fixedPC3834]; rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3501 = 4624 := by
  calc
    Artifact.submissionArtifact.instructionPC 3501 =
        Artifact.submissionArtifact.instructionPC 3500 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3500 (.op .MLOAD) (by rfl)
    _ = 4624 := by rw [fixedPC3835]; rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3502 = 4626 := by
  calc
    Artifact.submissionArtifact.instructionPC 3502 =
        Artifact.submissionArtifact.instructionPC 3501 + ((.push 1 160) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3501 (.push 1 160) (by rfl)
    _ = 4626 := by rw [fixedPC3836]; rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3503 = 4627 := by
  calc
    Artifact.submissionArtifact.instructionPC 3503 =
        Artifact.submissionArtifact.instructionPC 3502 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3502 (.op .MLOAD) (by rfl)
    _ = 4627 := by rw [fixedPC3837]; rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3504 = 4628 := by
  calc
    Artifact.submissionArtifact.instructionPC 3504 =
        Artifact.submissionArtifact.instructionPC 3503 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3503 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4628 := by rw [fixedPC3838]; rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3505 = 4629 := by
  calc
    Artifact.submissionArtifact.instructionPC 3505 =
        Artifact.submissionArtifact.instructionPC 3504 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3504 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4629 := by rw [fixedPC3839]; rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3506 = 4630 := by
  calc
    Artifact.submissionArtifact.instructionPC 3506 =
        Artifact.submissionArtifact.instructionPC 3505 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3505 (.op .GT) (by rfl)
    _ = 4630 := by rw [fixedPC3840]; rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3507 = 4631 := by
  calc
    Artifact.submissionArtifact.instructionPC 3507 =
        Artifact.submissionArtifact.instructionPC 3506 + ((.op (.Swap ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3506 (.op (.Swap ⟨1, by decide⟩)) (by rfl)
    _ = 4631 := by rw [fixedPC3841]; rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3508 = 4632 := by
  calc
    Artifact.submissionArtifact.instructionPC 3508 =
        Artifact.submissionArtifact.instructionPC 3507 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3507 (.op .SUB) (by rfl)
    _ = 4632 := by rw [fixedPC3842]; rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3509 = 4633 := by
  calc
    Artifact.submissionArtifact.instructionPC 3509 =
        Artifact.submissionArtifact.instructionPC 3508 + ((.op (.Dup ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3508 (.op (.Dup ⟨2, by decide⟩)) (by rfl)
    _ = 4633 := by rw [fixedPC3843]; rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3510 = 4634 := by
  calc
    Artifact.submissionArtifact.instructionPC 3510 =
        Artifact.submissionArtifact.instructionPC 3509 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3509 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4634 := by rw [fixedPC3844]; rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3511 = 4635 := by
  calc
    Artifact.submissionArtifact.instructionPC 3511 =
        Artifact.submissionArtifact.instructionPC 3510 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3510 (.op .SUB) (by rfl)
    _ = 4635 := by rw [fixedPC3845]; rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3512 = 4636 := by
  calc
    Artifact.submissionArtifact.instructionPC 3512 =
        Artifact.submissionArtifact.instructionPC 3511 + ((.op (.Swap ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3511 (.op (.Swap ⟨2, by decide⟩)) (by rfl)
    _ = 4636 := by rw [fixedPC3846]; rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3513 = 4637 := by
  calc
    Artifact.submissionArtifact.instructionPC 3513 =
        Artifact.submissionArtifact.instructionPC 3512 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3512 (.op .GT) (by rfl)
    _ = 4637 := by rw [fixedPC3847]; rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3514 = 4638 := by
  calc
    Artifact.submissionArtifact.instructionPC 3514 =
        Artifact.submissionArtifact.instructionPC 3513 + ((.op .OR) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3513 (.op .OR) (by rfl)
    _ = 4638 := by rw [fixedPC3848]; rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3515 = 4639 := by
  calc
    Artifact.submissionArtifact.instructionPC 3515 =
        Artifact.submissionArtifact.instructionPC 3514 + ((.op (.Swap ⟨0, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3514 (.op (.Swap ⟨0, by decide⟩)) (by rfl)
    _ = 4639 := by rw [fixedPC3849]; rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3516 = 4642 := by
  calc
    Artifact.submissionArtifact.instructionPC 3516 =
        Artifact.submissionArtifact.instructionPC 3515 + ((.push 2 1952) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3515 (.push 2 1952) (by rfl)
    _ = 4642 := by rw [fixedPC3850]; rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3517 = 4643 := by
  calc
    Artifact.submissionArtifact.instructionPC 3517 =
        Artifact.submissionArtifact.instructionPC 3516 + ((.op .MSTORE) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3516 (.op .MSTORE) (by rfl)
    _ = 4643 := by rw [fixedPC3851]; rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3518 = 4646 := by
  calc
    Artifact.submissionArtifact.instructionPC 3518 =
        Artifact.submissionArtifact.instructionPC 3517 + ((.push 2 2240) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3517 (.push 2 2240) (by rfl)
    _ = 4646 := by rw [fixedPC3852]; rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3519 = 4647 := by
  calc
    Artifact.submissionArtifact.instructionPC 3519 =
        Artifact.submissionArtifact.instructionPC 3518 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3518 (.op .MLOAD) (by rfl)
    _ = 4647 := by rw [fixedPC3853]; rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3520 = 4649 := by
  calc
    Artifact.submissionArtifact.instructionPC 3520 =
        Artifact.submissionArtifact.instructionPC 3519 + ((.push 1 128) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3519 (.push 1 128) (by rfl)
    _ = 4649 := by rw [fixedPC3854]; rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3521 = 4650 := by
  calc
    Artifact.submissionArtifact.instructionPC 3521 =
        Artifact.submissionArtifact.instructionPC 3520 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3520 (.op .MLOAD) (by rfl)
    _ = 4650 := by rw [fixedPC3855]; rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3522 = 4651 := by
  calc
    Artifact.submissionArtifact.instructionPC 3522 =
        Artifact.submissionArtifact.instructionPC 3521 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3521 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4651 := by rw [fixedPC3856]; rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3523 = 4652 := by
  calc
    Artifact.submissionArtifact.instructionPC 3523 =
        Artifact.submissionArtifact.instructionPC 3522 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3522 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4652 := by rw [fixedPC3857]; rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3524 = 4653 := by
  calc
    Artifact.submissionArtifact.instructionPC 3524 =
        Artifact.submissionArtifact.instructionPC 3523 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3523 (.op .GT) (by rfl)
    _ = 4653 := by rw [fixedPC3858]; rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3525 = 4654 := by
  calc
    Artifact.submissionArtifact.instructionPC 3525 =
        Artifact.submissionArtifact.instructionPC 3524 + ((.op (.Swap ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3524 (.op (.Swap ⟨1, by decide⟩)) (by rfl)
    _ = 4654 := by rw [fixedPC3859]; rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3526 = 4655 := by
  calc
    Artifact.submissionArtifact.instructionPC 3526 =
        Artifact.submissionArtifact.instructionPC 3525 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3525 (.op .SUB) (by rfl)
    _ = 4655 := by rw [fixedPC3860]; rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3527 = 4656 := by
  calc
    Artifact.submissionArtifact.instructionPC 3527 =
        Artifact.submissionArtifact.instructionPC 3526 + ((.op (.Dup ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3526 (.op (.Dup ⟨2, by decide⟩)) (by rfl)
    _ = 4656 := by rw [fixedPC3861]; rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3528 = 4657 := by
  calc
    Artifact.submissionArtifact.instructionPC 3528 =
        Artifact.submissionArtifact.instructionPC 3527 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3527 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4657 := by rw [fixedPC3862]; rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3529 = 4658 := by
  calc
    Artifact.submissionArtifact.instructionPC 3529 =
        Artifact.submissionArtifact.instructionPC 3528 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3528 (.op .SUB) (by rfl)
    _ = 4658 := by rw [fixedPC3863]; rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3530 = 4659 := by
  calc
    Artifact.submissionArtifact.instructionPC 3530 =
        Artifact.submissionArtifact.instructionPC 3529 + ((.op (.Swap ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3529 (.op (.Swap ⟨2, by decide⟩)) (by rfl)
    _ = 4659 := by rw [fixedPC3864]; rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3531 = 4660 := by
  calc
    Artifact.submissionArtifact.instructionPC 3531 =
        Artifact.submissionArtifact.instructionPC 3530 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3530 (.op .GT) (by rfl)
    _ = 4660 := by rw [fixedPC3865]; rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3532 = 4661 := by
  calc
    Artifact.submissionArtifact.instructionPC 3532 =
        Artifact.submissionArtifact.instructionPC 3531 + ((.op .OR) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3531 (.op .OR) (by rfl)
    _ = 4661 := by rw [fixedPC3866]; rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3533 = 4662 := by
  calc
    Artifact.submissionArtifact.instructionPC 3533 =
        Artifact.submissionArtifact.instructionPC 3532 + ((.op (.Swap ⟨0, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3532 (.op (.Swap ⟨0, by decide⟩)) (by rfl)
    _ = 4662 := by rw [fixedPC3867]; rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3534 = 4665 := by
  calc
    Artifact.submissionArtifact.instructionPC 3534 =
        Artifact.submissionArtifact.instructionPC 3533 + ((.push 2 1920) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3533 (.push 2 1920) (by rfl)
    _ = 4665 := by rw [fixedPC3868]; rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3535 = 4666 := by
  calc
    Artifact.submissionArtifact.instructionPC 3535 =
        Artifact.submissionArtifact.instructionPC 3534 + ((.op .MSTORE) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3534 (.op .MSTORE) (by rfl)
    _ = 4666 := by rw [fixedPC3869]; rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3536 = 4669 := by
  calc
    Artifact.submissionArtifact.instructionPC 3536 =
        Artifact.submissionArtifact.instructionPC 3535 + ((.push 2 2208) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3535 (.push 2 2208) (by rfl)
    _ = 4669 := by rw [fixedPC3871]; rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3537 = 4670 := by
  calc
    Artifact.submissionArtifact.instructionPC 3537 =
        Artifact.submissionArtifact.instructionPC 3536 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3536 (.op .MLOAD) (by rfl)
    _ = 4670 := by rw [fixedPC3872]; rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3538 = 4672 := by
  calc
    Artifact.submissionArtifact.instructionPC 3538 =
        Artifact.submissionArtifact.instructionPC 3537 + ((.push 1 96) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3537 (.push 1 96) (by rfl)
    _ = 4672 := by rw [fixedPC3873]; rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3539 = 4673 := by
  calc
    Artifact.submissionArtifact.instructionPC 3539 =
        Artifact.submissionArtifact.instructionPC 3538 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3538 (.op .MLOAD) (by rfl)
    _ = 4673 := by rw [fixedPC3874]; rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3540 = 4674 := by
  calc
    Artifact.submissionArtifact.instructionPC 3540 =
        Artifact.submissionArtifact.instructionPC 3539 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3539 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4674 := by rw [fixedPC3875]; rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3541 = 4675 := by
  calc
    Artifact.submissionArtifact.instructionPC 3541 =
        Artifact.submissionArtifact.instructionPC 3540 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3540 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4675 := by rw [fixedPC3876]; rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3542 = 4676 := by
  calc
    Artifact.submissionArtifact.instructionPC 3542 =
        Artifact.submissionArtifact.instructionPC 3541 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3541 (.op .GT) (by rfl)
    _ = 4676 := by rw [fixedPC3877]; rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3543 = 4677 := by
  calc
    Artifact.submissionArtifact.instructionPC 3543 =
        Artifact.submissionArtifact.instructionPC 3542 + ((.op (.Swap ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3542 (.op (.Swap ⟨1, by decide⟩)) (by rfl)
    _ = 4677 := by rw [fixedPC3878]; rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3544 = 4678 := by
  calc
    Artifact.submissionArtifact.instructionPC 3544 =
        Artifact.submissionArtifact.instructionPC 3543 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3543 (.op .SUB) (by rfl)
    _ = 4678 := by rw [fixedPC3879]; rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3545 = 4679 := by
  calc
    Artifact.submissionArtifact.instructionPC 3545 =
        Artifact.submissionArtifact.instructionPC 3544 + ((.op (.Dup ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3544 (.op (.Dup ⟨2, by decide⟩)) (by rfl)
    _ = 4679 := by rw [fixedPC3880]; rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3546 = 4680 := by
  calc
    Artifact.submissionArtifact.instructionPC 3546 =
        Artifact.submissionArtifact.instructionPC 3545 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3545 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4680 := by rw [fixedPC3881]; rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3547 = 4681 := by
  calc
    Artifact.submissionArtifact.instructionPC 3547 =
        Artifact.submissionArtifact.instructionPC 3546 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3546 (.op .SUB) (by rfl)
    _ = 4681 := by rw [fixedPC3882]; rfl


end Challenge.Modexp.Submission.Proofs.Fast
