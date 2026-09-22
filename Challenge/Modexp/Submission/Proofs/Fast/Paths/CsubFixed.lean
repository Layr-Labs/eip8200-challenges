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

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3449 .JUMPDEST,
   pushAt 3450 2 2688,
   opAt 3451 .MLOAD,
   pushAt 3452 1 128,
   opAt 3453 .EQ,
   pushAt 3454 2 4177,
   opAt 3455 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3449 .JUMPDEST,
   pushAt 3450 2 2688,
   opAt 3451 .MLOAD,
   pushAt 3452 1 128,
   opAt 3453 .EQ,
   pushAt 3454 2 4177,
   opAt 3455 .JUMPI,
   opAt 3345 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3456 2 2336,
   opAt 3457 .MLOAD,
   pushAt 3458 1 224,
   opAt 3459 .MLOAD,
   opAt 3460 (.Dup ⟨0, by decide⟩),
   opAt 3461 (.Dup ⟨2, by decide⟩),
   opAt 3462 .SUB,
   pushAt 3463 2 2016,
   opAt 3464 .MSTORE,
   opAt 3465 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3466 1 192,
   opAt 3467 .MLOAD,
   pushAt 3468 2 2304,
   opAt 3469 .MLOAD,
   opAt 3470 (.Dup ⟨1, by decide⟩),
   opAt 3471 (.Dup ⟨1, by decide⟩),
   opAt 3472 .SUB,
   opAt 3473 (.Swap ⟨1, by decide⟩),
   opAt 3474 .GT,
   opAt 3475 (.Swap ⟨1, by decide⟩),
   opAt 3476 (.Dup ⟨0, by decide⟩),
   opAt 3477 (.Dup ⟨2, by decide⟩),
   opAt 3478 .SUB,
   pushAt 3479 2 1984,
   opAt 3480 .MSTORE,
   opAt 3481 .GT,
   opAt 3482 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3483 1 160,
   opAt 3484 .MLOAD,
   pushAt 3485 2 2272,
   opAt 3486 .MLOAD,
   opAt 3487 (.Dup ⟨1, by decide⟩),
   opAt 3488 (.Dup ⟨1, by decide⟩),
   opAt 3489 .SUB,
   opAt 3490 (.Swap ⟨1, by decide⟩),
   opAt 3491 .GT,
   opAt 3492 (.Swap ⟨1, by decide⟩),
   opAt 3493 (.Dup ⟨0, by decide⟩),
   opAt 3494 (.Dup ⟨2, by decide⟩),
   opAt 3495 .SUB,
   pushAt 3496 2 1952,
   opAt 3497 .MSTORE,
   opAt 3498 .GT,
   opAt 3499 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3500 1 128,
   opAt 3501 .MLOAD,
   pushAt 3502 2 2240,
   opAt 3503 .MLOAD,
   opAt 3504 (.Dup ⟨1, by decide⟩),
   opAt 3505 (.Dup ⟨1, by decide⟩),
   opAt 3506 .SUB,
   opAt 3507 (.Swap ⟨1, by decide⟩),
   opAt 3508 .GT,
   opAt 3509 (.Swap ⟨1, by decide⟩),
   opAt 3510 (.Dup ⟨0, by decide⟩),
   opAt 3511 (.Dup ⟨2, by decide⟩),
   opAt 3512 .SUB,
   pushAt 3513 2 1920,
   opAt 3514 .MSTORE,
   opAt 3515 .GT,
   opAt 3516 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3517 1 96,
   opAt 3518 .MLOAD,
   pushAt 3519 2 2208,
   opAt 3520 .MLOAD,
   opAt 3521 (.Dup ⟨1, by decide⟩),
   opAt 3522 (.Dup ⟨1, by decide⟩),
   opAt 3523 .SUB,
   opAt 3524 (.Swap ⟨1, by decide⟩),
   opAt 3525 .GT,
   opAt 3526 (.Swap ⟨1, by decide⟩),
   opAt 3527 (.Dup ⟨0, by decide⟩),
   opAt 3528 (.Dup ⟨2, by decide⟩),
   opAt 3529 .SUB,
   pushAt 3530 2 1888,
   opAt 3531 .MSTORE,
   opAt 3532 .GT,
   opAt 3533 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3534 .JUMPDEST,
   pushAt 3535 1 64,
   opAt 3536 .MLOAD,
   pushAt 3537 2 2176,
   opAt 3538 .MLOAD,
   opAt 3539 (.Dup ⟨1, by decide⟩),
   opAt 3540 (.Dup ⟨1, by decide⟩),
   opAt 3541 .SUB,
   opAt 3542 (.Swap ⟨1, by decide⟩),
   opAt 3543 .GT,
   opAt 3544 (.Swap ⟨1, by decide⟩),
   opAt 3545 (.Dup ⟨0, by decide⟩),
   opAt 3546 (.Dup ⟨2, by decide⟩),
   opAt 3547 .SUB,
   pushAt 3548 2 1856,
   opAt 3549 .MSTORE,
   opAt 3550 .GT,
   opAt 3551 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3552 1 32,
   opAt 3553 .MLOAD,
   pushAt 3554 2 2144,
   opAt 3555 .MLOAD,
   opAt 3556 (.Dup ⟨1, by decide⟩),
   opAt 3557 (.Dup ⟨1, by decide⟩),
   opAt 3558 .SUB,
   opAt 3559 (.Swap ⟨1, by decide⟩),
   opAt 3560 .GT,
   opAt 3561 (.Swap ⟨1, by decide⟩),
   opAt 3562 (.Dup ⟨0, by decide⟩),
   opAt 3563 (.Dup ⟨2, by decide⟩),
   opAt 3564 .SUB,
   pushAt 3565 2 1824,
   opAt 3566 .MSTORE,
   opAt 3567 .GT,
   opAt 3568 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3569 0 0,
   opAt 3570 .MLOAD,
   pushAt 3571 2 2112,
   opAt 3572 .MLOAD,
   opAt 3573 (.Dup ⟨1, by decide⟩),
   opAt 3574 (.Dup ⟨1, by decide⟩),
   opAt 3575 .SUB,
   opAt 3576 (.Swap ⟨1, by decide⟩),
   opAt 3577 .GT,
   opAt 3578 (.Swap ⟨1, by decide⟩),
   opAt 3579 (.Dup ⟨0, by decide⟩),
   opAt 3580 (.Dup ⟨2, by decide⟩),
   opAt 3581 .SUB,
   pushAt 3582 2 1792,
   opAt 3583 .MSTORE,
   opAt 3584 .GT,
   opAt 3585 .OR]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3586 .ISZERO,
   pushAt 3587 2 2080,
   opAt 3588 .MLOAD,
   opAt 3589 .OR,
   pushAt 3590 2 319,
   opAt 3591 .NOT,
   pushAt 3592 2 4538,
   opAt 3593 .JUMP,
   opAt 3606 .JUMPDEST,
   opAt 3607 .MUL,
   pushAt 3608 2 2112,
   opAt 3609 .ADD,
   pushAt 3610 2 2688,
   opAt 3611 .MLOAD,
   opAt 3612 (.Swap ⟨1, by decide⟩),
   opAt 3613 .MCOPY,
   opAt 3614 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3346 2 2208,
   opAt 3347 .MLOAD,
   pushAt 3348 1 96,
   opAt 3349 .MLOAD,
   opAt 3350 (.Dup ⟨1, by decide⟩),
   opAt 3351 (.Dup ⟨1, by decide⟩),
   opAt 3352 .GT,
   opAt 3353 (.Swap ⟨1, by decide⟩),
   opAt 3354 .SUB,
   pushAt 3355 2 1888,
   opAt 3356 .MSTORE,
   pushAt 3357 2 4438,
   opAt 3358 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3534 .JUMPDEST,
   pushAt 3535 1 64,
   opAt 3536 .MLOAD,
   pushAt 3537 2 2176,
   opAt 3538 .MLOAD,
   opAt 3539 (.Dup ⟨1, by decide⟩),
   opAt 3540 (.Dup ⟨1, by decide⟩),
   opAt 3541 .SUB,
   opAt 3542 (.Swap ⟨1, by decide⟩),
   opAt 3543 .GT,
   opAt 3544 (.Swap ⟨1, by decide⟩),
   opAt 3545 (.Dup ⟨0, by decide⟩),
   opAt 3546 (.Dup ⟨2, by decide⟩),
   opAt 3547 .SUB,
   pushAt 3548 2 1856,
   opAt 3549 .MSTORE,
   opAt 3550 .GT,
   opAt 3551 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3552 1 32,
   opAt 3553 .MLOAD,
   pushAt 3554 2 2144,
   opAt 3555 .MLOAD,
   opAt 3556 (.Dup ⟨1, by decide⟩),
   opAt 3557 (.Dup ⟨1, by decide⟩),
   opAt 3558 .SUB,
   opAt 3559 (.Swap ⟨1, by decide⟩),
   opAt 3560 .GT,
   opAt 3561 (.Swap ⟨1, by decide⟩),
   opAt 3562 (.Dup ⟨0, by decide⟩),
   opAt 3563 (.Dup ⟨2, by decide⟩),
   opAt 3564 .SUB,
   pushAt 3565 2 1824,
   opAt 3566 .MSTORE,
   opAt 3567 .GT,
   opAt 3568 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3569 0 0,
   opAt 3570 .MLOAD,
   pushAt 3571 2 2112,
   opAt 3572 .MLOAD,
   opAt 3573 (.Dup ⟨1, by decide⟩),
   opAt 3574 (.Dup ⟨1, by decide⟩),
   opAt 3575 .SUB,
   opAt 3576 (.Swap ⟨1, by decide⟩),
   opAt 3577 .GT,
   opAt 3578 (.Swap ⟨1, by decide⟩),
   opAt 3579 (.Dup ⟨0, by decide⟩),
   opAt 3580 (.Dup ⟨2, by decide⟩),
   opAt 3581 .SUB,
   pushAt 3582 2 1792,
   opAt 3583 .MSTORE,
   opAt 3584 .GT,
   opAt 3585 .OR]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3586 .ISZERO,
   pushAt 3587 2 2080,
   opAt 3588 .MLOAD,
   opAt 3589 .OR,
   pushAt 3590 2 319,
   opAt 3591 .NOT,
   pushAt 3592 2 4538,
   opAt 3593 .JUMP,
   opAt 3606 .JUMPDEST,
   opAt 3607 .MUL,
   pushAt 3608 2 2112,
   opAt 3609 .ADD,
   pushAt 3610 2 2688,
   opAt 3611 .MLOAD,
   opAt 3612 (.Swap ⟨1, by decide⟩),
   opAt 3613 .MCOPY,
   opAt 3614 .JUMP]

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3445 = 4315 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4323 = true := by
  have h : Artifact.submissionArtifact.instructionPC 3449 = 4323 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [Artifact.instructionPC, h] using Artifact.isValidJumpDest_index 3449 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3585 = 4503 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3586 = 4504 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3587 = 4505 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3588 = 4508 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3589 = 4509 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3590 = 4510 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3591 = 4513 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3592 = 4514 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3593 = 4517 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3594 = 4518 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3595 = 4519 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3596 = 4522 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3597 = 4523 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3598 = 4526 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3599 = 4527 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3600 = 4528 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3601 = 4531 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3602 = 4534 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3603 = 4535 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3604 = 4536 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3604 = 4536 := fixedPC3797

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3604 = 4536 := fixedPC3797

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3605 = 4537 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3606 = 4538 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3607 = 4539 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3608 = 4540 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3609 = 4543 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : Artifact.submissionArtifact.instructionPC 3446 = 4316 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3115 : Artifact.submissionArtifact.instructionPC 3447 = 4319 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3116 : Artifact.submissionArtifact.instructionPC 3448 = 4320 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3117 : Artifact.submissionArtifact.instructionPC 3449 = 4323 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3118 : Artifact.submissionArtifact.instructionPC 3450 = 4324 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3119 : Artifact.submissionArtifact.instructionPC 3451 = 4327 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : Artifact.submissionArtifact.instructionPC 3341 = 4169 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4177 = true := by
  have h : Artifact.submissionArtifact.instructionPC 3345 = 4177 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [Artifact.instructionPC, h] using Artifact.isValidJumpDest_index 3345 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3452 = 4328 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3453 = 4330 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3454 = 4331 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3455 = 4334 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3456 = 4335 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3457 = 4338 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3458 = 4339 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3459 = 4341 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3460 = 4342 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3461 = 4343 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3462 = 4344 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3462 = 4344 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3463 = 4345 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3464 = 4348 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3465 = 4349 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3466 = 4350 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3467 = 4352 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3468 = 4353 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3469 = 4356 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3470 = 4357 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3471 = 4358 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3472 = 4359 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3473 = 4360 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3474 = 4361 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3475 = 4362 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3476 = 4363 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3477 = 4364 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3478 = 4365 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3479 = 4366 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3479 = 4366 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3480 = 4369 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3481 = 4370 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3482 = 4371 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3483 = 4372 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3484 = 4374 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3485 = 4375 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3486 = 4378 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3487 = 4379 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3488 = 4380 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3489 = 4381 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3490 = 4382 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3491 = 4383 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3492 = 4384 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3493 = 4385 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3494 = 4386 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3495 = 4387 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3496 = 4388 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3496 = 4388 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3497 = 4391 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3498 = 4392 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3499 = 4393 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3500 = 4394 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3501 = 4396 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3502 = 4397 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3503 = 4400 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3504 = 4401 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3505 = 4402 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3506 = 4403 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3507 = 4404 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3508 = 4405 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3509 = 4406 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3510 = 4407 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3511 = 4408 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3512 = 4409 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3513 = 4410 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3513 = 4410 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3514 = 4413 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3515 = 4414 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3516 = 4415 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3517 = 4416 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3518 = 4418 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3519 = 4419 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3520 = 4422 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3521 = 4423 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3522 = 4424 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3523 = 4425 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3524 = 4426 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3525 = 4427 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3526 = 4428 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3527 = 4429 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3528 = 4430 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3529 = 4431 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3530 = 4432 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3530 = 4432 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4438 = true := by
  have h : Artifact.submissionArtifact.instructionPC 3534 = 4438 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [Artifact.instructionPC, h] using Artifact.isValidJumpDest_index 3534 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3531 = 4435 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3532 = 4436 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3533 = 4437 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3534 = 4438 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3535 = 4439 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3536 = 4441 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3537 = 4442 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3538 = 4445 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3539 = 4446 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3540 = 4447 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3541 = 4448 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3542 = 4449 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3543 = 4450 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3544 = 4451 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3545 = 4452 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3546 = 4453 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3547 = 4454 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3548 = 4455 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3548 = 4455 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3549 = 4458 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3550 = 4459 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3551 = 4460 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3552 = 4461 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3553 = 4463 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3554 = 4464 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3555 = 4467 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3556 = 4468 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3557 = 4469 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3558 = 4470 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3559 = 4471 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3560 = 4472 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3561 = 4473 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3562 = 4474 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3563 = 4475 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3564 = 4476 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3565 = 4477 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3565 = 4477 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3566 = 4480 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3567 = 4481 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3568 = 4482 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3569 = 4483 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3570 = 4484 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3571 = 4485 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3572 = 4488 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3573 = 4489 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3574 = 4490 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3575 = 4491 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3576 = 4492 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3577 = 4493 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3578 = 4494 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3579 = 4495 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3580 = 4496 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3581 = 4497 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3582 = 4498 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3582 = 4498 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3583 = 4501 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3584 = 4502 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3585 = 4503 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3586 = 4504 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3603 = 4535 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3603 = 4535 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3604 = 4536 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3605 = 4537 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3606 = 4538 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3607 = 4539 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3608 = 4540 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3609 = 4543 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3610 = 4544 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4190 : Artifact.submissionArtifact.instructionPC 3355 = 4190 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4193 : Artifact.submissionArtifact.instructionPC 3356 = 4193 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4194 : Artifact.submissionArtifact.instructionPC 3357 = 4194 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4197 : Artifact.submissionArtifact.instructionPC 3358 = 4197 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4547 : Artifact.submissionArtifact.instructionPC 3611 = 4547 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4548 : Artifact.submissionArtifact.instructionPC 3612 = 4548 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4549 : Artifact.submissionArtifact.instructionPC 3613 = 4549 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4550 : Artifact.submissionArtifact.instructionPC 3614 = 4550 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3341 = 4169 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4177 = true := by
  have h : Artifact.submissionArtifact.instructionPC 3345 = 4177 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [Artifact.instructionPC, h] using Artifact.isValidJumpDest_index 3345 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3342 = 4172 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3343 = 4173 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3344 = 4176 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3345 = 4177 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3346 = 4178 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3347 = 4181 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3348 = 4182 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3349 = 4184 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3350 = 4185 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3351 = 4186 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3352 = 4187 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3353 = 4188 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3354 = 4189 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2665 = 3304 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3328 = 4152 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3329 = 4153 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3330 = 4154 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3331 = 4155 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3332 = 4156 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3333 = 4157 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3334 = 4158 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3335 = 4159 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3336 = 4162 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3337 = 4163 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3337 = 4163 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3338 = 4164 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3339 = 4167 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3340 = 4168 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2927 : Artifact.submissionArtifact.instructionPC 2665 = 3304 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3341 = 4169 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3342 = 4172 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3343 = 4173 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3344 = 4176 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3345 = 4177 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3346 = 4178 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3347 = 4181 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3348 = 4182 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3349 = 4184 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3350 = 4185 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3351 = 4186 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3352 = 4187 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3353 = 4188 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3354 = 4189 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3918 : Artifact.submissionArtifact.instructionPC 3587 = 4505 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3919 : Artifact.submissionArtifact.instructionPC 3588 = 4508 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3920 : Artifact.submissionArtifact.instructionPC 3589 = 4509 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 3595 = 4519 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 3596 = 4522 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 3597 = 4523 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 3598 = 4526 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 3599 = 4527 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 3600 = 4528 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 3601 = 4531 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 3602 = 4534 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast
