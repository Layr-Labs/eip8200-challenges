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

def csGenericPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3433 .JUMPDEST,
   pushAt 3434 2 2688,
   opAt 3435 .MLOAD,
   pushAt 3436 2 256,
   opAt 3437 .EQ,
   pushAt 3438 2 4580,
   opAt 3439 .JUMPI,
   pushAt 3440 2 2688,
   opAt 3441 .MLOAD,
   pushAt 3442 1 128,
   opAt 3443 .EQ,
   pushAt 3444 2 4341,
   opAt 3445 .JUMPI,
   pushAt 3446 2 2784,
   opAt 3447 .MLOAD,
   pushAt 3448 2 2752,
   opAt 3449 .MLOAD,
   opAt 3450 (.Dup ⟨0, by decide⟩),
   pushAt 3451 2 1792,
   opAt 3452 .ADD,
   opAt 3453 (.Swap ⟨0, by decide⟩),
   pushAt 3454 0 0,
   opAt 3455 (.Swap ⟨2, by decide⟩),
   pushAt 3456 2 1561,
   opAt 3457 .JUMP]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3433 .JUMPDEST,
   pushAt 3434 2 2688,
   opAt 3435 .MLOAD,
   pushAt 3436 2 256,
   opAt 3437 .EQ,
   pushAt 3438 2 4580,
   opAt 3439 .JUMPI,
   opAt 3458 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3433 .JUMPDEST,
   pushAt 3434 2 2688,
   opAt 3435 .MLOAD,
   pushAt 3436 2 256,
   opAt 3437 .EQ,
   pushAt 3438 2 4580,
   opAt 3439 .JUMPI,
   pushAt 3440 2 2688,
   opAt 3441 .MLOAD,
   pushAt 3442 1 128,
   opAt 3443 .EQ,
   pushAt 3444 2 4341,
   opAt 3445 .JUMPI,
   opAt 3288 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3459 2 2336,
   opAt 3460 .MLOAD,
   pushAt 3461 1 224,
   opAt 3462 .MLOAD,
   opAt 3463 (.Dup ⟨1, by decide⟩),
   opAt 3464 (.Dup ⟨1, by decide⟩),
   opAt 3465 .GT,
   opAt 3466 (.Swap ⟨1, by decide⟩),
   opAt 3467 .SUB,
   pushAt 3468 2 2016,
   opAt 3469 .MSTORE]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3470 2 2304,
   opAt 3471 .MLOAD,
   pushAt 3472 1 192,
   opAt 3473 .MLOAD,
   opAt 3474 (.Dup ⟨1, by decide⟩),
   opAt 3475 (.Dup ⟨1, by decide⟩),
   opAt 3476 .GT,
   opAt 3477 (.Swap ⟨1, by decide⟩),
   opAt 3478 .SUB,
   opAt 3479 (.Dup ⟨2, by decide⟩),
   opAt 3480 (.Dup ⟨1, by decide⟩),
   opAt 3481 .SUB,
   opAt 3482 (.Swap ⟨2, by decide⟩),
   opAt 3483 .GT,
   opAt 3484 .OR,
   opAt 3485 (.Swap ⟨0, by decide⟩),
   pushAt 3486 2 1984,
   opAt 3487 .MSTORE]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3488 2 2272,
   opAt 3489 .MLOAD,
   pushAt 3490 1 160,
   opAt 3491 .MLOAD,
   opAt 3492 (.Dup ⟨1, by decide⟩),
   opAt 3493 (.Dup ⟨1, by decide⟩),
   opAt 3494 .GT,
   opAt 3495 (.Swap ⟨1, by decide⟩),
   opAt 3496 .SUB,
   opAt 3497 (.Dup ⟨2, by decide⟩),
   opAt 3498 (.Dup ⟨1, by decide⟩),
   opAt 3499 .SUB,
   opAt 3500 (.Swap ⟨2, by decide⟩),
   opAt 3501 .GT,
   opAt 3502 .OR,
   opAt 3503 (.Swap ⟨0, by decide⟩),
   pushAt 3504 2 1952,
   opAt 3505 .MSTORE]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3506 2 2240,
   opAt 3507 .MLOAD,
   pushAt 3508 1 128,
   opAt 3509 .MLOAD,
   opAt 3510 (.Dup ⟨1, by decide⟩),
   opAt 3511 (.Dup ⟨1, by decide⟩),
   opAt 3512 .GT,
   opAt 3513 (.Swap ⟨1, by decide⟩),
   opAt 3514 .SUB,
   opAt 3515 (.Dup ⟨2, by decide⟩),
   opAt 3516 (.Dup ⟨1, by decide⟩),
   opAt 3517 .SUB,
   opAt 3518 (.Swap ⟨2, by decide⟩),
   opAt 3519 .GT,
   opAt 3520 .OR,
   opAt 3521 (.Swap ⟨0, by decide⟩),
   pushAt 3522 2 1920,
   opAt 3523 .MSTORE]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3524 2 2208,
   opAt 3525 .MLOAD,
   pushAt 3526 1 96,
   opAt 3527 .MLOAD,
   opAt 3528 (.Dup ⟨1, by decide⟩),
   opAt 3529 (.Dup ⟨1, by decide⟩),
   opAt 3530 .GT,
   opAt 3531 (.Swap ⟨1, by decide⟩),
   opAt 3532 .SUB,
   opAt 3533 (.Dup ⟨2, by decide⟩),
   opAt 3534 (.Dup ⟨1, by decide⟩),
   opAt 3535 .SUB,
   opAt 3536 (.Swap ⟨2, by decide⟩),
   opAt 3537 .GT,
   opAt 3538 .OR,
   opAt 3539 (.Swap ⟨0, by decide⟩),
   pushAt 3540 2 1888,
   opAt 3541 .MSTORE]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3542 .JUMPDEST,
   pushAt 3543 2 2176,
   opAt 3544 .MLOAD,
   pushAt 3545 1 64,
   opAt 3546 .MLOAD,
   opAt 3547 (.Dup ⟨1, by decide⟩),
   opAt 3548 (.Dup ⟨1, by decide⟩),
   opAt 3549 .GT,
   opAt 3550 (.Swap ⟨1, by decide⟩),
   opAt 3551 .SUB,
   opAt 3552 (.Dup ⟨2, by decide⟩),
   opAt 3553 (.Dup ⟨1, by decide⟩),
   opAt 3554 .SUB,
   opAt 3555 (.Swap ⟨2, by decide⟩),
   opAt 3556 .GT,
   opAt 3557 .OR,
   opAt 3558 (.Swap ⟨0, by decide⟩),
   pushAt 3559 2 1856,
   opAt 3560 .MSTORE]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3561 2 2144,
   opAt 3562 .MLOAD,
   pushAt 3563 1 32,
   opAt 3564 .MLOAD,
   opAt 3565 (.Dup ⟨1, by decide⟩),
   opAt 3566 (.Dup ⟨1, by decide⟩),
   opAt 3567 .GT,
   opAt 3568 (.Swap ⟨1, by decide⟩),
   opAt 3569 .SUB,
   opAt 3570 (.Dup ⟨2, by decide⟩),
   opAt 3571 (.Dup ⟨1, by decide⟩),
   opAt 3572 .SUB,
   opAt 3573 (.Swap ⟨2, by decide⟩),
   opAt 3574 .GT,
   opAt 3575 .OR,
   opAt 3576 (.Swap ⟨0, by decide⟩),
   pushAt 3577 2 1824,
   opAt 3578 .MSTORE]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3579 2 2112,
   opAt 3580 .MLOAD,
   pushAt 3581 0 0,
   opAt 3582 .MLOAD,
   opAt 3583 (.Dup ⟨1, by decide⟩),
   opAt 3584 (.Dup ⟨1, by decide⟩),
   opAt 3585 .GT,
   opAt 3586 (.Swap ⟨1, by decide⟩),
   opAt 3587 .SUB,
   opAt 3588 (.Dup ⟨2, by decide⟩),
   opAt 3589 (.Dup ⟨1, by decide⟩),
   opAt 3590 .SUB,
   opAt 3591 (.Swap ⟨2, by decide⟩),
   opAt 3592 .GT,
   opAt 3593 .OR,
   opAt 3594 (.Swap ⟨0, by decide⟩),
   pushAt 3595 2 1792,
   opAt 3596 .MSTORE]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3597 .ISZERO,
   pushAt 3598 2 2080,
   opAt 3599 .MLOAD,
   opAt 3600 .OR,
   pushAt 3601 2 319,
   opAt 3602 .NOT,
   pushAt 3603 2 4772,
   opAt 3604 .JUMP,
   opAt 3605 .JUMPDEST,
   opAt 3606 .MUL,
   pushAt 3607 2 2112,
   opAt 3608 .ADD,
   pushAt 3609 2 2688,
   opAt 3610 .MLOAD,
   opAt 3611 (.Swap ⟨1, by decide⟩),
   opAt 3612 .MCOPY,
   opAt 3613 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3289 2 2208,
   opAt 3290 .MLOAD,
   pushAt 3291 1 96,
   opAt 3292 .MLOAD,
   opAt 3293 (.Dup ⟨1, by decide⟩),
   opAt 3294 (.Dup ⟨1, by decide⟩),
   opAt 3295 .GT,
   opAt 3296 (.Swap ⟨1, by decide⟩),
   opAt 3297 .SUB,
   pushAt 3298 2 1888,
   opAt 3299 .MSTORE,
   pushAt 3300 2 4689,
   opAt 3301 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3542 .JUMPDEST,
   pushAt 3543 2 2176,
   opAt 3544 .MLOAD,
   pushAt 3545 1 64,
   opAt 3546 .MLOAD,
   opAt 3547 (.Dup ⟨1, by decide⟩),
   opAt 3548 (.Dup ⟨1, by decide⟩),
   opAt 3549 .GT,
   opAt 3550 (.Swap ⟨1, by decide⟩),
   opAt 3551 .SUB,
   opAt 3552 (.Dup ⟨2, by decide⟩),
   opAt 3553 (.Dup ⟨1, by decide⟩),
   opAt 3554 .SUB,
   opAt 3555 (.Swap ⟨2, by decide⟩),
   opAt 3556 .GT,
   opAt 3557 .OR,
   opAt 3558 (.Swap ⟨0, by decide⟩),
   pushAt 3559 2 1856,
   opAt 3560 .MSTORE]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3561 2 2144,
   opAt 3562 .MLOAD,
   pushAt 3563 1 32,
   opAt 3564 .MLOAD,
   opAt 3565 (.Dup ⟨1, by decide⟩),
   opAt 3566 (.Dup ⟨1, by decide⟩),
   opAt 3567 .GT,
   opAt 3568 (.Swap ⟨1, by decide⟩),
   opAt 3569 .SUB,
   opAt 3570 (.Dup ⟨2, by decide⟩),
   opAt 3571 (.Dup ⟨1, by decide⟩),
   opAt 3572 .SUB,
   opAt 3573 (.Swap ⟨2, by decide⟩),
   opAt 3574 .GT,
   opAt 3575 .OR,
   opAt 3576 (.Swap ⟨0, by decide⟩),
   pushAt 3577 2 1824,
   opAt 3578 .MSTORE]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3579 2 2112,
   opAt 3580 .MLOAD,
   pushAt 3581 0 0,
   opAt 3582 .MLOAD,
   opAt 3583 (.Dup ⟨1, by decide⟩),
   opAt 3584 (.Dup ⟨1, by decide⟩),
   opAt 3585 .GT,
   opAt 3586 (.Swap ⟨1, by decide⟩),
   opAt 3587 .SUB,
   opAt 3588 (.Dup ⟨2, by decide⟩),
   opAt 3589 (.Dup ⟨1, by decide⟩),
   opAt 3590 .SUB,
   opAt 3591 (.Swap ⟨2, by decide⟩),
   opAt 3592 .GT,
   opAt 3593 .OR,
   opAt 3594 (.Swap ⟨0, by decide⟩),
   pushAt 3595 2 1792,
   opAt 3596 .MSTORE]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3597 .ISZERO,
   pushAt 3598 2 2080,
   opAt 3599 .MLOAD,
   opAt 3600 .OR,
   pushAt 3601 2 319,
   opAt 3602 .NOT,
   pushAt 3603 2 4772,
   opAt 3604 .JUMP,
   opAt 3605 .JUMPDEST,
   opAt 3606 .MUL,
   pushAt 3607 2 2112,
   opAt 3608 .ADD,
   pushAt 3609 2 2688,
   opAt 3610 .MLOAD,
   opAt 3611 (.Swap ⟨1, by decide⟩),
   opAt 3612 .MCOPY,
   opAt 3613 .JUMP]

@[simp] theorem fixedPC1618 : Artifact.submissionArtifact.instructionPC 1102 = 1557 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC1619 : Artifact.submissionArtifact.instructionPC 1103 = 1560 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3433 = 4536 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4536 = true := by
  simpa only [Artifact.instructionPC, fixedPC3777] using Artifact.isValidJumpDest_index 3433 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3434 = 4537 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3435 = 4540 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3436 = 4541 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3437 = 4544 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3438 = 4545 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3439 = 4548 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3440 = 4549 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3441 = 4552 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3442 = 4553 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3443 = 4555 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3444 = 4556 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3445 = 4559 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3446 = 4560 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3447 = 4563 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3448 = 4564 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3449 = 4567 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3450 = 4568 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3451 = 4569 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3452 = 4572 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3453 = 4573 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3453 = 4573 := fixedPC3797

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3453 = 4573 := fixedPC3797

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3454 = 4574 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3455 = 4575 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3456 = 4576 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3457 = 4579 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3458 = 4580 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5023 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4580 = true := by
  simpa only [Artifact.instructionPC, fixedPC3804] using Artifact.isValidJumpDest_index 3458 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3459 = 4581 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3460 = 4584 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3461 = 4585 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3462 = 4587 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3463 = 4588 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3464 = 4589 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3465 = 4590 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3466 = 4591 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3467 = 4592 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3468 = 4593 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3469 = 4596 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3470 = 4597 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3471 = 4600 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3472 = 4601 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3473 = 4603 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3474 = 4604 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3475 = 4605 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3476 = 4606 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3477 = 4607 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3478 = 4608 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3479 = 4609 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3480 = 4610 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3481 = 4611 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3482 = 4612 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3483 = 4613 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3484 = 4614 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3485 = 4615 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3486 = 4616 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3487 = 4619 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3488 = 4620 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3489 = 4623 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3490 = 4624 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3491 = 4626 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3492 = 4627 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3493 = 4628 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3494 = 4629 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3495 = 4630 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3496 = 4631 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3497 = 4632 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3498 = 4633 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3499 = 4634 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3500 = 4635 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3501 = 4636 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3502 = 4637 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3503 = 4638 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3504 = 4639 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3505 = 4642 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3506 = 4643 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3507 = 4646 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3508 = 4647 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3509 = 4649 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3510 = 4650 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3511 = 4651 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3512 = 4652 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3513 = 4653 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3514 = 4654 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3515 = 4655 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3516 = 4656 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3517 = 4657 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3518 = 4658 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3519 = 4659 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3520 = 4660 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3521 = 4661 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3522 = 4662 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3523 = 4665 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3524 = 4666 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3525 = 4669 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3526 = 4670 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3527 = 4672 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3528 = 4673 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3529 = 4674 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3530 = 4675 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3531 = 4676 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3532 = 4677 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3533 = 4678 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3534 = 4679 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3535 = 4680 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3536 = 4681 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3537 = 4682 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3538 = 4683 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3539 = 4684 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3540 = 4685 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3541 = 4688 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3542 = 4689 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4689 = true := by
  simpa only [Artifact.instructionPC, fixedPC3889] using Artifact.isValidJumpDest_index 3542 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3543 = 4690 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3544 = 4693 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3545 = 4694 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3546 = 4696 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3547 = 4697 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3548 = 4698 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3549 = 4699 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3550 = 4700 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3551 = 4701 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3552 = 4702 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3553 = 4703 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3554 = 4704 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3555 = 4705 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3556 = 4706 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3557 = 4707 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3558 = 4708 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3559 = 4709 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3560 = 4712 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3561 = 4713 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3562 = 4716 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3563 = 4717 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3564 = 4719 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3565 = 4720 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3566 = 4721 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3567 = 4722 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3568 = 4723 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3569 = 4724 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3570 = 4725 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3571 = 4726 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3572 = 4727 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3573 = 4728 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3574 = 4729 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3575 = 4730 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3576 = 4731 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3577 = 4732 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3578 = 4735 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3579 = 4736 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3580 = 4739 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3581 = 4740 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3582 = 4741 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3583 = 4742 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3584 = 4743 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3585 = 4744 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3586 = 4745 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3587 = 4746 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3588 = 4747 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3589 = 4748 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3590 = 4749 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3591 = 4750 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3592 = 4751 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3593 = 4752 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3594 = 4753 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3595 = 4754 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3596 = 4757 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3597 = 4758 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3598 = 4759 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3599 = 4762 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3600 = 4763 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3601 = 4764 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3606 = 4773 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3606 = 4773 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3607 = 4774 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3608 = 4777 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3609 = 4778 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3610 = 4781 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3611 = 4782 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3612 = 4783 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3613 = 4784 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3958 : Artifact.submissionArtifact.instructionPC 0 = 0 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3959 : Artifact.submissionArtifact.instructionPC 0 = 0 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3960 : Artifact.submissionArtifact.instructionPC 1 = 1 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3961 : Artifact.submissionArtifact.instructionPC 2 = 2 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3962 : Artifact.submissionArtifact.instructionPC 3 = 4 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3963 : Artifact.submissionArtifact.instructionPC 4 = 5 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3964 : Artifact.submissionArtifact.instructionPC 5 = 7 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3965 : Artifact.submissionArtifact.instructionPC 6 = 8 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3966 : Artifact.submissionArtifact.instructionPC 7 = 10 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3967 : Artifact.submissionArtifact.instructionPC 8 = 11 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3968 : Artifact.submissionArtifact.instructionPC 9 = 12 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3969 : Artifact.submissionArtifact.instructionPC 10 = 13 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3970 : Artifact.submissionArtifact.instructionPC 11 = 15 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3971 : Artifact.submissionArtifact.instructionPC 12 = 16 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3972 : Artifact.submissionArtifact.instructionPC 13 = 17 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3973 : Artifact.submissionArtifact.instructionPC 14 = 18 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3974 : Artifact.submissionArtifact.instructionPC 15 = 20 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3975 : Artifact.submissionArtifact.instructionPC 16 = 21 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3976 : Artifact.submissionArtifact.instructionPC 17 = 22 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3977 : Artifact.submissionArtifact.instructionPC 18 = 24 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3978 : Artifact.submissionArtifact.instructionPC 19 = 25 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3979 : Artifact.submissionArtifact.instructionPC 20 = 26 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3980 : Artifact.submissionArtifact.instructionPC 21 = 28 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3981 : Artifact.submissionArtifact.instructionPC 22 = 29 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3982 : Artifact.submissionArtifact.instructionPC 23 = 30 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3983 : Artifact.submissionArtifact.instructionPC 24 = 31 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3984 : Artifact.submissionArtifact.instructionPC 25 = 32 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3985 : Artifact.submissionArtifact.instructionPC 26 = 35 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3986 : Artifact.submissionArtifact.instructionPC 27 = 36 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3987 : Artifact.submissionArtifact.instructionPC 28 = 37 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3988 : Artifact.submissionArtifact.instructionPC 29 = 39 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3989 : Artifact.submissionArtifact.instructionPC 30 = 40 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3990 : Artifact.submissionArtifact.instructionPC 31 = 41 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3991 : Artifact.submissionArtifact.instructionPC 32 = 42 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3992 : Artifact.submissionArtifact.instructionPC 32 = 42 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3993 : Artifact.submissionArtifact.instructionPC 70 = 125 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5272 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 125 = true := by
  simpa only [Artifact.instructionPC, fixedPC3993] using Artifact.isValidJumpDest_index 70 (by rfl)

@[simp] theorem fixedPC3994 : Artifact.submissionArtifact.instructionPC 71 = 126 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3995 : Artifact.submissionArtifact.instructionPC 72 = 127 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3996 : Artifact.submissionArtifact.instructionPC 73 = 128 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3997 : Artifact.submissionArtifact.instructionPC 74 = 129 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3998 : Artifact.submissionArtifact.instructionPC 75 = 132 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3288 = 4341 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4341 = true := by
  simpa only [Artifact.instructionPC, fixedPC3999] using Artifact.isValidJumpDest_index 3288 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3289 = 4342 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3290 = 4345 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3291 = 4346 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3292 = 4348 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3293 = 4349 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3294 = 4350 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3295 = 4351 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3296 = 4352 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3297 = 4353 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3298 = 4354 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3299 = 4357 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3300 = 4358 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3301 = 4361 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2471 = 3295 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3275 = 4320 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3276 = 4321 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3277 = 4322 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3278 = 4323 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3279 = 4326 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3280 = 4327 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3281 = 4328 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3282 = 4331 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3283 = 4332 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3284 = 4333 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3284 = 4333 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3285 = 4336 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3286 = 4337 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3287 = 4340 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2927 : Artifact.submissionArtifact.instructionPC 2471 = 3295 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3288 = 4341 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3289 = 4342 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3290 = 4345 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3291 = 4346 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3292 = 4348 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3293 = 4349 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3294 = 4350 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3295 = 4351 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3296 = 4352 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3297 = 4353 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3298 = 4354 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3299 = 4357 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3300 = 4358 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3301 = 4361 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3918 : Artifact.submissionArtifact.instructionPC 3602 = 4767 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3919 : Artifact.submissionArtifact.instructionPC 3603 = 4768 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3920 : Artifact.submissionArtifact.instructionPC 3604 = 4771 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 3322 = 4398 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 3323 = 4399 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 3324 = 4402 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 3325 = 4405 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 3326 = 4406 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 3327 = 4407 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 3328 = 4408 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 3605 = 4772 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast
