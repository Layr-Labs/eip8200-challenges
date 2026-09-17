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
  [opAt 3415 .JUMPDEST,
   pushAt 3416 2 2688,
   opAt 3417 .MLOAD,
   pushAt 3418 1 128,
   opAt 3419 .EQ,
   pushAt 3420 2 4098,
   opAt 3421 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3415 .JUMPDEST,
   pushAt 3416 2 2688,
   opAt 3417 .MLOAD,
   pushAt 3418 1 128,
   opAt 3419 .EQ,
   pushAt 3420 2 4098,
   opAt 3421 .JUMPI,
   opAt 3311 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3422 2 2336,
   opAt 3423 .MLOAD,
   pushAt 3424 1 224,
   opAt 3425 .MLOAD,
   opAt 3426 (.Dup ⟨0, by decide⟩),
   opAt 3427 (.Dup ⟨2, by decide⟩),
   opAt 3428 .SUB,
   pushAt 3429 3 2016,
   opAt 3430 .MSTORE,
   opAt 3431 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3432 1 192,
   opAt 3433 .MLOAD,
   pushAt 3434 2 2304,
   opAt 3435 .MLOAD,
   opAt 3436 (.Dup ⟨1, by decide⟩),
   opAt 3437 (.Dup ⟨1, by decide⟩),
   opAt 3438 .SUB,
   opAt 3439 (.Swap ⟨1, by decide⟩),
   opAt 3440 .GT,
   opAt 3441 (.Swap ⟨1, by decide⟩),
   opAt 3442 (.Dup ⟨0, by decide⟩),
   opAt 3443 (.Dup ⟨2, by decide⟩),
   opAt 3444 .SUB,
   pushAt 3445 3 1984,
   opAt 3446 .MSTORE,
   opAt 3447 .GT,
   opAt 3448 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3449 1 160,
   opAt 3450 .MLOAD,
   pushAt 3451 2 2272,
   opAt 3452 .MLOAD,
   opAt 3453 (.Dup ⟨1, by decide⟩),
   opAt 3454 (.Dup ⟨1, by decide⟩),
   opAt 3455 .SUB,
   opAt 3456 (.Swap ⟨1, by decide⟩),
   opAt 3457 .GT,
   opAt 3458 (.Swap ⟨1, by decide⟩),
   opAt 3459 (.Dup ⟨0, by decide⟩),
   opAt 3460 (.Dup ⟨2, by decide⟩),
   opAt 3461 .SUB,
   pushAt 3462 3 1952,
   opAt 3463 .MSTORE,
   opAt 3464 .GT,
   opAt 3465 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3466 1 128,
   opAt 3467 .MLOAD,
   pushAt 3468 2 2240,
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
   pushAt 3479 3 1920,
   opAt 3480 .MSTORE,
   opAt 3481 .GT,
   opAt 3482 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3483 1 96,
   opAt 3484 .MLOAD,
   pushAt 3485 2 2208,
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
   pushAt 3496 3 1888,
   opAt 3497 .MSTORE,
   opAt 3498 .GT,
   opAt 3499 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3500 .JUMPDEST,
   pushAt 3501 1 64,
   opAt 3502 .MLOAD,
   pushAt 3503 2 2176,
   opAt 3504 .MLOAD,
   opAt 3505 (.Dup ⟨1, by decide⟩),
   opAt 3506 (.Dup ⟨1, by decide⟩),
   opAt 3507 .SUB,
   opAt 3508 (.Swap ⟨1, by decide⟩),
   opAt 3509 .GT,
   opAt 3510 (.Swap ⟨1, by decide⟩),
   opAt 3511 (.Dup ⟨0, by decide⟩),
   opAt 3512 (.Dup ⟨2, by decide⟩),
   opAt 3513 .SUB,
   pushAt 3514 3 1856,
   opAt 3515 .MSTORE,
   opAt 3516 .GT,
   opAt 3517 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3518 1 32,
   opAt 3519 .MLOAD,
   pushAt 3520 2 2144,
   opAt 3521 .MLOAD,
   opAt 3522 (.Dup ⟨1, by decide⟩),
   opAt 3523 (.Dup ⟨1, by decide⟩),
   opAt 3524 .SUB,
   opAt 3525 (.Swap ⟨1, by decide⟩),
   opAt 3526 .GT,
   opAt 3527 (.Swap ⟨1, by decide⟩),
   opAt 3528 (.Dup ⟨0, by decide⟩),
   opAt 3529 (.Dup ⟨2, by decide⟩),
   opAt 3530 .SUB,
   pushAt 3531 3 1824,
   opAt 3532 .MSTORE,
   opAt 3533 .GT,
   opAt 3534 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3535 0 0,
   opAt 3536 .MLOAD,
   pushAt 3537 2 2112,
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
   pushAt 3548 3 1792,
   opAt 3549 .MSTORE,
   opAt 3550 .GT,
   opAt 3551 .OR]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3552 .ISZERO,
   pushAt 3553 2 2080,
   opAt 3554 .MLOAD,
   opAt 3555 .OR,
   pushAt 3556 2 319,
   opAt 3557 .NOT,
   pushAt 3558 2 4467,
   opAt 3559 .JUMP,
   opAt 3572 .JUMPDEST,
   opAt 3573 .MUL,
   pushAt 3574 2 2112,
   opAt 3575 .ADD,
   pushAt 3576 2 2688,
   opAt 3577 .MLOAD,
   opAt 3578 (.Swap ⟨1, by decide⟩),
   opAt 3579 .MCOPY,
   opAt 3580 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3312 2 2208,
   opAt 3313 .MLOAD,
   pushAt 3314 1 96,
   opAt 3315 .MLOAD,
   opAt 3316 (.Dup ⟨1, by decide⟩),
   opAt 3317 (.Dup ⟨1, by decide⟩),
   opAt 3318 .GT,
   opAt 3319 (.Swap ⟨1, by decide⟩),
   opAt 3320 .SUB,
   pushAt 3321 2 1888,
   opAt 3322 .MSTORE,
   pushAt 3323 2 4364,
   opAt 3324 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3500 .JUMPDEST,
   pushAt 3501 1 64,
   opAt 3502 .MLOAD,
   pushAt 3503 2 2176,
   opAt 3504 .MLOAD,
   opAt 3505 (.Dup ⟨1, by decide⟩),
   opAt 3506 (.Dup ⟨1, by decide⟩),
   opAt 3507 .SUB,
   opAt 3508 (.Swap ⟨1, by decide⟩),
   opAt 3509 .GT,
   opAt 3510 (.Swap ⟨1, by decide⟩),
   opAt 3511 (.Dup ⟨0, by decide⟩),
   opAt 3512 (.Dup ⟨2, by decide⟩),
   opAt 3513 .SUB,
   pushAt 3514 3 1856,
   opAt 3515 .MSTORE,
   opAt 3516 .GT,
   opAt 3517 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3518 1 32,
   opAt 3519 .MLOAD,
   pushAt 3520 2 2144,
   opAt 3521 .MLOAD,
   opAt 3522 (.Dup ⟨1, by decide⟩),
   opAt 3523 (.Dup ⟨1, by decide⟩),
   opAt 3524 .SUB,
   opAt 3525 (.Swap ⟨1, by decide⟩),
   opAt 3526 .GT,
   opAt 3527 (.Swap ⟨1, by decide⟩),
   opAt 3528 (.Dup ⟨0, by decide⟩),
   opAt 3529 (.Dup ⟨2, by decide⟩),
   opAt 3530 .SUB,
   pushAt 3531 3 1824,
   opAt 3532 .MSTORE,
   opAt 3533 .GT,
   opAt 3534 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3535 0 0,
   opAt 3536 .MLOAD,
   pushAt 3537 2 2112,
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
   pushAt 3548 3 1792,
   opAt 3549 .MSTORE,
   opAt 3550 .GT,
   opAt 3551 .OR]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3552 .ISZERO,
   pushAt 3553 2 2080,
   opAt 3554 .MLOAD,
   opAt 3555 .OR,
   pushAt 3556 2 319,
   opAt 3557 .NOT,
   pushAt 3558 2 4467,
   opAt 3559 .JUMP,
   opAt 3572 .JUMPDEST,
   opAt 3573 .MUL,
   pushAt 3574 2 2112,
   opAt 3575 .ADD,
   pushAt 3576 2 2688,
   opAt 3577 .MLOAD,
   opAt 3578 (.Swap ⟨1, by decide⟩),
   opAt 3579 .MCOPY,
   opAt 3580 .JUMP]

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3415 = 4244 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4244 = true := by
  simpa only [Artifact.instructionPC, fixedPC3777] using Artifact.isValidJumpDest_index 3415 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3555 = 4438 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3556 = 4439 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3557 = 4442 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3558 = 4443 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3559 = 4446 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3560 = 4447 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3561 = 4448 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3562 = 4451 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3563 = 4452 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3564 = 4455 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3565 = 4456 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3566 = 4457 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3567 = 4460 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3568 = 4463 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3569 = 4464 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3570 = 4465 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3571 = 4466 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3572 = 4467 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3573 = 4468 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3574 = 4469 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3574 = 4469 := fixedPC3797

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3574 = 4469 := fixedPC3797

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3575 = 4472 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3576 = 4473 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3577 = 4476 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3578 = 4477 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3579 = 4478 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : Artifact.submissionArtifact.instructionPC 3416 = 4245 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3115 : Artifact.submissionArtifact.instructionPC 3417 = 4248 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3116 : Artifact.submissionArtifact.instructionPC 3418 = 4249 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3117 : Artifact.submissionArtifact.instructionPC 3419 = 4251 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3118 : Artifact.submissionArtifact.instructionPC 3420 = 4252 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3119 : Artifact.submissionArtifact.instructionPC 3421 = 4255 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4343 through index 3277, which is now an `MCOPY` at 4364, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : Artifact.submissionArtifact.instructionPC 3311 = 4098 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4098 = true := by
  simpa only [Artifact.instructionPC, fixedPC3009] using Artifact.isValidJumpDest_index 3311 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3422 = 4256 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3423 = 4259 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3424 = 4260 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3425 = 4262 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3426 = 4263 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3427 = 4264 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3428 = 4265 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3429 = 4266 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3430 = 4270 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3431 = 4271 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3432 = 4272 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3432 = 4272 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3433 = 4274 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3434 = 4275 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3435 = 4278 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3436 = 4279 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3437 = 4280 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3438 = 4281 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3439 = 4282 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3440 = 4283 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3441 = 4284 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3442 = 4285 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3443 = 4286 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3444 = 4287 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3445 = 4288 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3446 = 4292 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3447 = 4293 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3448 = 4294 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3449 = 4295 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3449 = 4295 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3450 = 4297 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3451 = 4298 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3452 = 4301 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3453 = 4302 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3454 = 4303 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3455 = 4304 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3456 = 4305 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3457 = 4306 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3458 = 4307 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3459 = 4308 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3460 = 4309 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3461 = 4310 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3462 = 4311 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3463 = 4315 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3464 = 4316 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3465 = 4317 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3466 = 4318 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3466 = 4318 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3467 = 4320 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3468 = 4321 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3469 = 4324 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3470 = 4325 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3471 = 4326 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3472 = 4327 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3473 = 4328 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3474 = 4329 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3475 = 4330 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3476 = 4331 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3477 = 4332 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3478 = 4333 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3479 = 4334 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3480 = 4338 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3481 = 4339 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3482 = 4340 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3483 = 4341 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3483 = 4341 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3484 = 4343 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3485 = 4344 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3486 = 4347 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3487 = 4348 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3488 = 4349 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3489 = 4350 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3490 = 4351 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3491 = 4352 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3492 = 4353 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3493 = 4354 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3494 = 4355 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3495 = 4356 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3496 = 4357 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3497 = 4361 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3498 = 4362 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3499 = 4363 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3500 = 4364 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3500 = 4364 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4364 = true := by
  simpa only [Artifact.instructionPC, fixedPC3889] using Artifact.isValidJumpDest_index 3500 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3501 = 4365 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3502 = 4367 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3503 = 4368 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3504 = 4371 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3505 = 4372 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3506 = 4373 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3507 = 4374 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3508 = 4375 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3509 = 4376 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3510 = 4377 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3511 = 4378 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3512 = 4379 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3513 = 4380 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3514 = 4381 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3515 = 4385 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3516 = 4386 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3517 = 4387 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3518 = 4388 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3518 = 4388 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3519 = 4390 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3520 = 4391 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3521 = 4394 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3522 = 4395 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3523 = 4396 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3524 = 4397 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3525 = 4398 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3526 = 4399 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3527 = 4400 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3528 = 4401 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3529 = 4402 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3530 = 4403 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3531 = 4404 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3532 = 4408 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3533 = 4409 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3534 = 4410 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3535 = 4411 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3535 = 4411 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3536 = 4412 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3537 = 4413 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3538 = 4416 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3539 = 4417 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3540 = 4418 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3541 = 4419 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3542 = 4420 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3543 = 4421 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3544 = 4422 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3545 = 4423 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3546 = 4424 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3547 = 4425 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3548 = 4426 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3549 = 4430 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3550 = 4431 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3551 = 4432 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3552 = 4433 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3552 = 4433 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3553 = 4434 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3554 = 4437 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3555 = 4438 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3556 = 4439 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3573 = 4468 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3573 = 4468 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3574 = 4469 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3575 = 4472 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3576 = 4473 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3577 = 4476 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3578 = 4477 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3579 = 4478 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3580 = 4479 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3311 = 4098 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4098 = true := by
  simpa only [Artifact.instructionPC, fixedPC3999] using Artifact.isValidJumpDest_index 3311 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3312 = 4099 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3313 = 4102 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3314 = 4103 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3315 = 4105 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3316 = 4106 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3317 = 4107 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3318 = 4108 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3319 = 4109 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3320 = 4110 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3321 = 4111 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3322 = 4114 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3323 = 4115 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3324 = 4118 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2644 = 3245 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3298 = 4077 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3299 = 4078 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3300 = 4079 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3301 = 4080 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3302 = 4083 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3303 = 4084 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3304 = 4085 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3305 = 4088 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3306 = 4089 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3307 = 4090 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3307 = 4090 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3308 = 4093 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3309 = 4094 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3310 = 4097 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2927 : Artifact.submissionArtifact.instructionPC 2644 = 3245 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3311 = 4098 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3312 = 4099 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3313 = 4102 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3314 = 4103 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3315 = 4105 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3316 = 4106 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3317 = 4107 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3318 = 4108 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3319 = 4109 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3320 = 4110 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3321 = 4111 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3322 = 4114 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3323 = 4115 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3324 = 4118 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3918 : Artifact.submissionArtifact.instructionPC 3557 = 4442 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3919 : Artifact.submissionArtifact.instructionPC 3558 = 4443 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3920 : Artifact.submissionArtifact.instructionPC 3559 = 4446 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 3565 = 4456 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 3566 = 4457 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 3567 = 4460 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 3568 = 4463 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 3569 = 4464 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 3570 = 4465 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 3571 = 4466 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 3572 = 4467 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast
