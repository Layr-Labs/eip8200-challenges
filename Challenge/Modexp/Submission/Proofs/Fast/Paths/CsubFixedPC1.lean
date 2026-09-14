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

@[simp] theorem fixedPC1618 : Artifact.submissionArtifact.instructionPC 1104 = 1558 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC1619 : Artifact.submissionArtifact.instructionPC 1105 = 1561 := by
  calc
    Artifact.submissionArtifact.instructionPC 1105 =
        Artifact.submissionArtifact.instructionPC 1104 + ((.push 2 4320) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1104 (.push 2 4320) (by rfl)
    _ = 1561 := by rw [fixedPC1618]; rfl

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3444 = 4536 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4536 = true := by
  simpa only [Artifact.instructionPC, fixedPC3777] using Artifact.isValidJumpDest_index 3444 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3445 = 4537 := by
  calc
    Artifact.submissionArtifact.instructionPC 3445 =
        Artifact.submissionArtifact.instructionPC 3444 + ((.op .JUMPDEST) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3444 (.op .JUMPDEST) (by rfl)
    _ = 4537 := by rw [fixedPC3777]; rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3446 = 4540 := by
  calc
    Artifact.submissionArtifact.instructionPC 3446 =
        Artifact.submissionArtifact.instructionPC 3445 + ((.push 2 2688) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3445 (.push 2 2688) (by rfl)
    _ = 4540 := by rw [fixedPC3778]; rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3447 = 4541 := by
  calc
    Artifact.submissionArtifact.instructionPC 3447 =
        Artifact.submissionArtifact.instructionPC 3446 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3446 (.op .MLOAD) (by rfl)
    _ = 4541 := by rw [fixedPC3779]; rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3448 = 4544 := by
  calc
    Artifact.submissionArtifact.instructionPC 3448 =
        Artifact.submissionArtifact.instructionPC 3447 + ((.push 2 256) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3447 (.push 2 256) (by rfl)
    _ = 4544 := by rw [fixedPC3780]; rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3449 = 4545 := by
  calc
    Artifact.submissionArtifact.instructionPC 3449 =
        Artifact.submissionArtifact.instructionPC 3448 + ((.op .EQ) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3448 (.op .EQ) (by rfl)
    _ = 4545 := by rw [fixedPC3781]; rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3450 = 4548 := by
  calc
    Artifact.submissionArtifact.instructionPC 3450 =
        Artifact.submissionArtifact.instructionPC 3449 + ((.push 2 4580) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3449 (.push 2 4580) (by rfl)
    _ = 4548 := by rw [fixedPC3782]; rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3451 = 4549 := by
  calc
    Artifact.submissionArtifact.instructionPC 3451 =
        Artifact.submissionArtifact.instructionPC 3450 + ((.op .JUMPI) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3450 (.op .JUMPI) (by rfl)
    _ = 4549 := by rw [fixedPC3783]; rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3452 = 4552 := by
  calc
    Artifact.submissionArtifact.instructionPC 3452 =
        Artifact.submissionArtifact.instructionPC 3451 + ((.push 2 2688) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3451 (.push 2 2688) (by rfl)
    _ = 4552 := by rw [fixedPC3784]; rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3453 = 4553 := by
  calc
    Artifact.submissionArtifact.instructionPC 3453 =
        Artifact.submissionArtifact.instructionPC 3452 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3452 (.op .MLOAD) (by rfl)
    _ = 4553 := by rw [fixedPC3785]; rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3454 = 4555 := by
  calc
    Artifact.submissionArtifact.instructionPC 3454 =
        Artifact.submissionArtifact.instructionPC 3453 + ((.push 1 128) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3453 (.push 1 128) (by rfl)
    _ = 4555 := by rw [fixedPC3786]; rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3455 = 4556 := by
  calc
    Artifact.submissionArtifact.instructionPC 3455 =
        Artifact.submissionArtifact.instructionPC 3454 + ((.op .EQ) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3454 (.op .EQ) (by rfl)
    _ = 4556 := by rw [fixedPC3787]; rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3456 = 4559 := by
  calc
    Artifact.submissionArtifact.instructionPC 3456 =
        Artifact.submissionArtifact.instructionPC 3455 + ((.push 2 4341) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3455 (.push 2 4341) (by rfl)
    _ = 4559 := by rw [fixedPC3788]; rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3457 = 4560 := by
  calc
    Artifact.submissionArtifact.instructionPC 3457 =
        Artifact.submissionArtifact.instructionPC 3456 + ((.op .JUMPI) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3456 (.op .JUMPI) (by rfl)
    _ = 4560 := by rw [fixedPC3789]; rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3458 = 4563 := by
  calc
    Artifact.submissionArtifact.instructionPC 3458 =
        Artifact.submissionArtifact.instructionPC 3457 + ((.push 2 2784) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3457 (.push 2 2784) (by rfl)
    _ = 4563 := by rw [fixedPC3790]; rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3459 = 4564 := by
  calc
    Artifact.submissionArtifact.instructionPC 3459 =
        Artifact.submissionArtifact.instructionPC 3458 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3458 (.op .MLOAD) (by rfl)
    _ = 4564 := by rw [fixedPC3791]; rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3460 = 4567 := by
  calc
    Artifact.submissionArtifact.instructionPC 3460 =
        Artifact.submissionArtifact.instructionPC 3459 + ((.push 2 2752) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3459 (.push 2 2752) (by rfl)
    _ = 4567 := by rw [fixedPC3792]; rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3461 = 4568 := by
  calc
    Artifact.submissionArtifact.instructionPC 3461 =
        Artifact.submissionArtifact.instructionPC 3460 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3460 (.op .MLOAD) (by rfl)
    _ = 4568 := by rw [fixedPC3793]; rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3462 = 4569 := by
  calc
    Artifact.submissionArtifact.instructionPC 3462 =
        Artifact.submissionArtifact.instructionPC 3461 + ((.op (.Dup ⟨0, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3461 (.op (.Dup ⟨0, by decide⟩)) (by rfl)
    _ = 4569 := by rw [fixedPC3794]; rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3463 = 4572 := by
  calc
    Artifact.submissionArtifact.instructionPC 3463 =
        Artifact.submissionArtifact.instructionPC 3462 + ((.push 2 1792) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3462 (.push 2 1792) (by rfl)
    _ = 4572 := by rw [fixedPC3795]; rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3464 = 4573 := by
  calc
    Artifact.submissionArtifact.instructionPC 3464 =
        Artifact.submissionArtifact.instructionPC 3463 + ((.op .ADD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3463 (.op .ADD) (by rfl)
    _ = 4573 := by rw [fixedPC3796]; rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3464 = 4573 := fixedPC3797

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3464 = 4573 := fixedPC3797

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3465 = 4574 := by
  calc
    Artifact.submissionArtifact.instructionPC 3465 =
        Artifact.submissionArtifact.instructionPC 3464 + ((.op (.Swap ⟨0, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3464 (.op (.Swap ⟨0, by decide⟩)) (by rfl)
    _ = 4574 := by rw [fixedPC3797]; rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3466 = 4575 := by
  calc
    Artifact.submissionArtifact.instructionPC 3466 =
        Artifact.submissionArtifact.instructionPC 3465 + ((.push 0 0) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3465 (.push 0 0) (by rfl)
    _ = 4575 := by rw [fixedPC3800]; rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3467 = 4576 := by
  calc
    Artifact.submissionArtifact.instructionPC 3467 =
        Artifact.submissionArtifact.instructionPC 3466 + ((.op (.Swap ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3466 (.op (.Swap ⟨2, by decide⟩)) (by rfl)
    _ = 4576 := by rw [fixedPC3801]; rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3468 = 4579 := by
  calc
    Artifact.submissionArtifact.instructionPC 3468 =
        Artifact.submissionArtifact.instructionPC 3467 + ((.push 2 1562) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3467 (.push 2 1562) (by rfl)
    _ = 4579 := by rw [fixedPC3802]; rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3469 = 4580 := by
  calc
    Artifact.submissionArtifact.instructionPC 3469 =
        Artifact.submissionArtifact.instructionPC 3468 + ((.op .JUMP) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3468 (.op .JUMP) (by rfl)
    _ = 4580 := by rw [fixedPC3803]; rfl

@[simp] theorem fixedJump5023 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4580 = true := by
  simpa only [Artifact.instructionPC, fixedPC3804] using Artifact.isValidJumpDest_index 3469 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3470 = 4581 := by
  calc
    Artifact.submissionArtifact.instructionPC 3470 =
        Artifact.submissionArtifact.instructionPC 3469 + ((.op .JUMPDEST) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3469 (.op .JUMPDEST) (by rfl)
    _ = 4581 := by rw [fixedPC3804]; rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3471 = 4584 := by
  calc
    Artifact.submissionArtifact.instructionPC 3471 =
        Artifact.submissionArtifact.instructionPC 3470 + ((.push 2 2336) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3470 (.push 2 2336) (by rfl)
    _ = 4584 := by rw [fixedPC3805]; rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3472 = 4585 := by
  calc
    Artifact.submissionArtifact.instructionPC 3472 =
        Artifact.submissionArtifact.instructionPC 3471 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3471 (.op .MLOAD) (by rfl)
    _ = 4585 := by rw [fixedPC3806]; rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3473 = 4587 := by
  calc
    Artifact.submissionArtifact.instructionPC 3473 =
        Artifact.submissionArtifact.instructionPC 3472 + ((.push 1 224) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3472 (.push 1 224) (by rfl)
    _ = 4587 := by rw [fixedPC3807]; rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3474 = 4588 := by
  calc
    Artifact.submissionArtifact.instructionPC 3474 =
        Artifact.submissionArtifact.instructionPC 3473 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3473 (.op .MLOAD) (by rfl)
    _ = 4588 := by rw [fixedPC3808]; rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3475 = 4589 := by
  calc
    Artifact.submissionArtifact.instructionPC 3475 =
        Artifact.submissionArtifact.instructionPC 3474 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3474 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4589 := by rw [fixedPC3809]; rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3476 = 4590 := by
  calc
    Artifact.submissionArtifact.instructionPC 3476 =
        Artifact.submissionArtifact.instructionPC 3475 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3475 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4590 := by rw [fixedPC3810]; rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3477 = 4591 := by
  calc
    Artifact.submissionArtifact.instructionPC 3477 =
        Artifact.submissionArtifact.instructionPC 3476 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3476 (.op .GT) (by rfl)
    _ = 4591 := by rw [fixedPC3811]; rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3478 = 4592 := by
  calc
    Artifact.submissionArtifact.instructionPC 3478 =
        Artifact.submissionArtifact.instructionPC 3477 + ((.op (.Swap ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3477 (.op (.Swap ⟨1, by decide⟩)) (by rfl)
    _ = 4592 := by rw [fixedPC3812]; rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3479 = 4593 := by
  calc
    Artifact.submissionArtifact.instructionPC 3479 =
        Artifact.submissionArtifact.instructionPC 3478 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3478 (.op .SUB) (by rfl)
    _ = 4593 := by rw [fixedPC3813]; rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3480 = 4596 := by
  calc
    Artifact.submissionArtifact.instructionPC 3480 =
        Artifact.submissionArtifact.instructionPC 3479 + ((.push 2 2016) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3479 (.push 2 2016) (by rfl)
    _ = 4596 := by rw [fixedPC3814]; rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3481 = 4597 := by
  calc
    Artifact.submissionArtifact.instructionPC 3481 =
        Artifact.submissionArtifact.instructionPC 3480 + ((.op .MSTORE) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3480 (.op .MSTORE) (by rfl)
    _ = 4597 := by rw [fixedPC3815]; rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3482 = 4600 := by
  calc
    Artifact.submissionArtifact.instructionPC 3482 =
        Artifact.submissionArtifact.instructionPC 3481 + ((.push 2 2304) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3481 (.push 2 2304) (by rfl)
    _ = 4600 := by rw [fixedPC3816]; rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3483 = 4601 := by
  calc
    Artifact.submissionArtifact.instructionPC 3483 =
        Artifact.submissionArtifact.instructionPC 3482 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3482 (.op .MLOAD) (by rfl)
    _ = 4601 := by rw [fixedPC3817]; rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3484 = 4603 := by
  calc
    Artifact.submissionArtifact.instructionPC 3484 =
        Artifact.submissionArtifact.instructionPC 3483 + ((.push 1 192) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3483 (.push 1 192) (by rfl)
    _ = 4603 := by rw [fixedPC3818]; rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3485 = 4604 := by
  calc
    Artifact.submissionArtifact.instructionPC 3485 =
        Artifact.submissionArtifact.instructionPC 3484 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3484 (.op .MLOAD) (by rfl)
    _ = 4604 := by rw [fixedPC3819]; rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3486 = 4605 := by
  calc
    Artifact.submissionArtifact.instructionPC 3486 =
        Artifact.submissionArtifact.instructionPC 3485 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3485 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4605 := by rw [fixedPC3820]; rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3487 = 4606 := by
  calc
    Artifact.submissionArtifact.instructionPC 3487 =
        Artifact.submissionArtifact.instructionPC 3486 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3486 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4606 := by rw [fixedPC3821]; rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3488 = 4607 := by
  calc
    Artifact.submissionArtifact.instructionPC 3488 =
        Artifact.submissionArtifact.instructionPC 3487 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3487 (.op .GT) (by rfl)
    _ = 4607 := by rw [fixedPC3822]; rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3489 = 4608 := by
  calc
    Artifact.submissionArtifact.instructionPC 3489 =
        Artifact.submissionArtifact.instructionPC 3488 + ((.op (.Swap ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3488 (.op (.Swap ⟨1, by decide⟩)) (by rfl)
    _ = 4608 := by rw [fixedPC3823]; rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3490 = 4609 := by
  calc
    Artifact.submissionArtifact.instructionPC 3490 =
        Artifact.submissionArtifact.instructionPC 3489 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3489 (.op .SUB) (by rfl)
    _ = 4609 := by rw [fixedPC3824]; rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3491 = 4610 := by
  calc
    Artifact.submissionArtifact.instructionPC 3491 =
        Artifact.submissionArtifact.instructionPC 3490 + ((.op (.Dup ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3490 (.op (.Dup ⟨2, by decide⟩)) (by rfl)
    _ = 4610 := by rw [fixedPC3825]; rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3492 = 4611 := by
  calc
    Artifact.submissionArtifact.instructionPC 3492 =
        Artifact.submissionArtifact.instructionPC 3491 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3491 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4611 := by rw [fixedPC3826]; rfl


end Challenge.Modexp.Submission.Proofs.Fast
