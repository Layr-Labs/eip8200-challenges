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
  [opAt 3417 .JUMPDEST,
   pushAt 3418 2 2688,
   opAt 3419 .MLOAD,
   pushAt 3420 2 256,
   opAt 3421 .EQ,
   pushAt 3422 2 4553,
   opAt 3423 .JUMPI,
   pushAt 3424 2 2688,
   opAt 3425 .MLOAD,
   pushAt 3426 1 128,
   opAt 3427 .EQ,
   pushAt 3428 2 4370,
   opAt 3429 .JUMPI,
   pushAt 3430 2 2784,
   opAt 3431 .MLOAD,
   pushAt 3432 2 2752,
   opAt 3433 .MLOAD,
   opAt 3434 (.Dup ⟨0, by decide⟩),
   pushAt 3435 2 1792,
   opAt 3436 .ADD,
   opAt 3437 (.Swap ⟨0, by decide⟩),
   pushAt 3438 0 0,
   opAt 3439 (.Swap ⟨2, by decide⟩),
   pushAt 3440 2 1566,
   opAt 3441 .JUMP]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3417 .JUMPDEST,
   pushAt 3418 2 2688,
   opAt 3419 .MLOAD,
   pushAt 3420 2 256,
   opAt 3421 .EQ,
   pushAt 3422 2 4553,
   opAt 3423 .JUMPI,
   opAt 3442 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3417 .JUMPDEST,
   pushAt 3418 2 2688,
   opAt 3419 .MLOAD,
   pushAt 3420 2 256,
   opAt 3421 .EQ,
   pushAt 3422 2 4553,
   opAt 3423 .JUMPI,
   pushAt 3424 2 2688,
   opAt 3425 .MLOAD,
   pushAt 3426 1 128,
   opAt 3427 .EQ,
   pushAt 3428 2 4370,
   opAt 3429 .JUMPI,
   opAt 3315 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3443 2 2336,
   opAt 3444 .MLOAD,
   pushAt 3445 1 224,
   opAt 3446 .MLOAD,
   opAt 3447 (.Dup ⟨1, by decide⟩),
   opAt 3448 (.Dup ⟨1, by decide⟩),
   opAt 3449 .GT,
   opAt 3450 (.Swap ⟨1, by decide⟩),
   opAt 3451 .SUB,
   pushAt 3452 2 2016,
   opAt 3453 .MSTORE]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3454 2 2304,
   opAt 3455 .MLOAD,
   pushAt 3456 1 192,
   opAt 3457 .MLOAD,
   opAt 3458 (.Dup ⟨1, by decide⟩),
   opAt 3459 (.Dup ⟨1, by decide⟩),
   opAt 3460 .GT,
   opAt 3461 (.Swap ⟨1, by decide⟩),
   opAt 3462 .SUB,
   opAt 3463 (.Dup ⟨2, by decide⟩),
   opAt 3464 (.Dup ⟨1, by decide⟩),
   opAt 3465 .SUB,
   opAt 3466 (.Swap ⟨2, by decide⟩),
   opAt 3467 .GT,
   opAt 3468 .OR,
   opAt 3469 (.Swap ⟨0, by decide⟩),
   pushAt 3470 2 1984,
   opAt 3471 .MSTORE]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3472 2 2272,
   opAt 3473 .MLOAD,
   pushAt 3474 1 160,
   opAt 3475 .MLOAD,
   opAt 3476 (.Dup ⟨1, by decide⟩),
   opAt 3477 (.Dup ⟨1, by decide⟩),
   opAt 3478 .GT,
   opAt 3479 (.Swap ⟨1, by decide⟩),
   opAt 3480 .SUB,
   opAt 3481 (.Dup ⟨2, by decide⟩),
   opAt 3482 (.Dup ⟨1, by decide⟩),
   opAt 3483 .SUB,
   opAt 3484 (.Swap ⟨2, by decide⟩),
   opAt 3485 .GT,
   opAt 3486 .OR,
   opAt 3487 (.Swap ⟨0, by decide⟩),
   pushAt 3488 2 1952,
   opAt 3489 .MSTORE]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3490 2 2240,
   opAt 3491 .MLOAD,
   pushAt 3492 1 128,
   opAt 3493 .MLOAD,
   opAt 3494 (.Dup ⟨1, by decide⟩),
   opAt 3495 (.Dup ⟨1, by decide⟩),
   opAt 3496 .GT,
   opAt 3497 (.Swap ⟨1, by decide⟩),
   opAt 3498 .SUB,
   opAt 3499 (.Dup ⟨2, by decide⟩),
   opAt 3500 (.Dup ⟨1, by decide⟩),
   opAt 3501 .SUB,
   opAt 3502 (.Swap ⟨2, by decide⟩),
   opAt 3503 .GT,
   opAt 3504 .OR,
   opAt 3505 (.Swap ⟨0, by decide⟩),
   pushAt 3506 2 1920,
   opAt 3507 .MSTORE]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 3508 2 2208,
   opAt 3509 .MLOAD,
   pushAt 3510 1 96,
   opAt 3511 .MLOAD,
   opAt 3512 (.Dup ⟨1, by decide⟩),
   opAt 3513 (.Dup ⟨1, by decide⟩),
   opAt 3514 .GT,
   opAt 3515 (.Swap ⟨1, by decide⟩),
   opAt 3516 .SUB,
   opAt 3517 (.Dup ⟨2, by decide⟩),
   opAt 3518 (.Dup ⟨1, by decide⟩),
   opAt 3519 .SUB,
   opAt 3520 (.Swap ⟨2, by decide⟩),
   opAt 3521 .GT,
   opAt 3522 .OR,
   opAt 3523 (.Swap ⟨0, by decide⟩),
   pushAt 3524 2 1888,
   opAt 3525 .MSTORE]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3526 .JUMPDEST,
   pushAt 3527 2 2176,
   opAt 3528 .MLOAD,
   pushAt 3529 1 64,
   opAt 3530 .MLOAD,
   opAt 3531 (.Dup ⟨1, by decide⟩),
   opAt 3532 (.Dup ⟨1, by decide⟩),
   opAt 3533 .GT,
   opAt 3534 (.Swap ⟨1, by decide⟩),
   opAt 3535 .SUB,
   opAt 3536 (.Dup ⟨2, by decide⟩),
   opAt 3537 (.Dup ⟨1, by decide⟩),
   opAt 3538 .SUB,
   opAt 3539 (.Swap ⟨2, by decide⟩),
   opAt 3540 .GT,
   opAt 3541 .OR,
   opAt 3542 (.Swap ⟨0, by decide⟩),
   pushAt 3543 2 1856,
   opAt 3544 .MSTORE]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3545 2 2144,
   opAt 3546 .MLOAD,
   pushAt 3547 1 32,
   opAt 3548 .MLOAD,
   opAt 3549 (.Dup ⟨1, by decide⟩),
   opAt 3550 (.Dup ⟨1, by decide⟩),
   opAt 3551 .GT,
   opAt 3552 (.Swap ⟨1, by decide⟩),
   opAt 3553 .SUB,
   opAt 3554 (.Dup ⟨2, by decide⟩),
   opAt 3555 (.Dup ⟨1, by decide⟩),
   opAt 3556 .SUB,
   opAt 3557 (.Swap ⟨2, by decide⟩),
   opAt 3558 .GT,
   opAt 3559 .OR,
   opAt 3560 (.Swap ⟨0, by decide⟩),
   pushAt 3561 2 1824,
   opAt 3562 .MSTORE]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3563 2 2112,
   opAt 3564 .MLOAD,
   pushAt 3565 0 0,
   opAt 3566 .MLOAD,
   opAt 3567 (.Dup ⟨1, by decide⟩),
   opAt 3568 (.Dup ⟨1, by decide⟩),
   opAt 3569 .GT,
   opAt 3570 (.Swap ⟨1, by decide⟩),
   opAt 3571 .SUB,
   opAt 3572 (.Dup ⟨2, by decide⟩),
   opAt 3573 (.Dup ⟨1, by decide⟩),
   opAt 3574 .SUB,
   opAt 3575 (.Swap ⟨2, by decide⟩),
   opAt 3576 .GT,
   opAt 3577 .OR,
   opAt 3578 (.Swap ⟨0, by decide⟩),
   pushAt 3579 2 1792,
   opAt 3580 .MSTORE]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3581 .ISZERO,
   pushAt 3582 2 2080,
   opAt 3583 .MLOAD,
   opAt 3584 .OR,
   pushAt 3585 2 319,
   opAt 3586 .NOT,
   pushAt 3587 2 4756,
   opAt 3588 .JUMP,
   opAt 3596 .JUMPDEST,
   opAt 3597 .MUL,
   pushAt 3598 2 2112,
   opAt 3599 .ADD,
   pushAt 3600 2 2688,
   opAt 3601 .MLOAD,
   opAt 3602 (.Swap ⟨1, by decide⟩),
   opAt 3603 .MCOPY,
   opAt 3604 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3316 2 2208,
   opAt 3317 .MLOAD,
   pushAt 3318 1 96,
   opAt 3319 .MLOAD,
   opAt 3320 (.Dup ⟨1, by decide⟩),
   opAt 3321 (.Dup ⟨1, by decide⟩),
   opAt 3322 .GT,
   opAt 3323 (.Swap ⟨1, by decide⟩),
   opAt 3324 .SUB,
   pushAt 3325 2 1888,
   opAt 3326 .MSTORE,
   pushAt 3327 2 4662,
   opAt 3328 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3526 .JUMPDEST,
   pushAt 3527 2 2176,
   opAt 3528 .MLOAD,
   pushAt 3529 1 64,
   opAt 3530 .MLOAD,
   opAt 3531 (.Dup ⟨1, by decide⟩),
   opAt 3532 (.Dup ⟨1, by decide⟩),
   opAt 3533 .GT,
   opAt 3534 (.Swap ⟨1, by decide⟩),
   opAt 3535 .SUB,
   opAt 3536 (.Dup ⟨2, by decide⟩),
   opAt 3537 (.Dup ⟨1, by decide⟩),
   opAt 3538 .SUB,
   opAt 3539 (.Swap ⟨2, by decide⟩),
   opAt 3540 .GT,
   opAt 3541 .OR,
   opAt 3542 (.Swap ⟨0, by decide⟩),
   pushAt 3543 2 1856,
   opAt 3544 .MSTORE]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3545 2 2144,
   opAt 3546 .MLOAD,
   pushAt 3547 1 32,
   opAt 3548 .MLOAD,
   opAt 3549 (.Dup ⟨1, by decide⟩),
   opAt 3550 (.Dup ⟨1, by decide⟩),
   opAt 3551 .GT,
   opAt 3552 (.Swap ⟨1, by decide⟩),
   opAt 3553 .SUB,
   opAt 3554 (.Dup ⟨2, by decide⟩),
   opAt 3555 (.Dup ⟨1, by decide⟩),
   opAt 3556 .SUB,
   opAt 3557 (.Swap ⟨2, by decide⟩),
   opAt 3558 .GT,
   opAt 3559 .OR,
   opAt 3560 (.Swap ⟨0, by decide⟩),
   pushAt 3561 2 1824,
   opAt 3562 .MSTORE]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3563 2 2112,
   opAt 3564 .MLOAD,
   pushAt 3565 0 0,
   opAt 3566 .MLOAD,
   opAt 3567 (.Dup ⟨1, by decide⟩),
   opAt 3568 (.Dup ⟨1, by decide⟩),
   opAt 3569 .GT,
   opAt 3570 (.Swap ⟨1, by decide⟩),
   opAt 3571 .SUB,
   opAt 3572 (.Dup ⟨2, by decide⟩),
   opAt 3573 (.Dup ⟨1, by decide⟩),
   opAt 3574 .SUB,
   opAt 3575 (.Swap ⟨2, by decide⟩),
   opAt 3576 .GT,
   opAt 3577 .OR,
   opAt 3578 (.Swap ⟨0, by decide⟩),
   pushAt 3579 2 1792,
   opAt 3580 .MSTORE]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3581 .ISZERO,
   pushAt 3582 2 2080,
   opAt 3583 .MLOAD,
   opAt 3584 .OR,
   pushAt 3585 2 319,
   opAt 3586 .NOT,
   pushAt 3587 2 4756,
   opAt 3588 .JUMP,
   opAt 3596 .JUMPDEST,
   opAt 3597 .MUL,
   pushAt 3598 2 2112,
   opAt 3599 .ADD,
   pushAt 3600 2 2688,
   opAt 3601 .MLOAD,
   opAt 3602 (.Swap ⟨1, by decide⟩),
   opAt 3603 .MCOPY,
   opAt 3604 .JUMP]

@[simp] theorem fixedPC1618 : Artifact.submissionArtifact.instructionPC 1105 = 1562 := by rfl

@[simp] theorem fixedPC1619 : Artifact.submissionArtifact.instructionPC 1106 = 1565 := by
  calc
    Artifact.submissionArtifact.instructionPC 1106 =
        Artifact.submissionArtifact.instructionPC 1105 + (YulEvmCompiler.Instr.push 2 4349).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1105 _ (by rfl)
    _ = 1565 := by rw [fixedPC1618]; rfl

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3417 = 4509 := by rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4509 = true := by
  simpa only [Artifact.instructionPC, fixedPC3777] using Artifact.isValidJumpDest_index 3417 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3418 = 4510 := by
  calc
    Artifact.submissionArtifact.instructionPC 3418 =
        Artifact.submissionArtifact.instructionPC 3417 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3417 _ (by rfl)
    _ = 4510 := by rw [fixedPC3777]; rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3419 = 4513 := by
  calc
    Artifact.submissionArtifact.instructionPC 3419 =
        Artifact.submissionArtifact.instructionPC 3418 + (YulEvmCompiler.Instr.push 2 2688).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3418 _ (by rfl)
    _ = 4513 := by rw [fixedPC3778]; rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3420 = 4514 := by
  calc
    Artifact.submissionArtifact.instructionPC 3420 =
        Artifact.submissionArtifact.instructionPC 3419 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3419 _ (by rfl)
    _ = 4514 := by rw [fixedPC3779]; rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3421 = 4517 := by
  calc
    Artifact.submissionArtifact.instructionPC 3421 =
        Artifact.submissionArtifact.instructionPC 3420 + (YulEvmCompiler.Instr.push 2 256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3420 _ (by rfl)
    _ = 4517 := by rw [fixedPC3780]; rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3422 = 4518 := by
  calc
    Artifact.submissionArtifact.instructionPC 3422 =
        Artifact.submissionArtifact.instructionPC 3421 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3421 _ (by rfl)
    _ = 4518 := by rw [fixedPC3781]; rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3423 = 4521 := by
  calc
    Artifact.submissionArtifact.instructionPC 3423 =
        Artifact.submissionArtifact.instructionPC 3422 + (YulEvmCompiler.Instr.push 2 4553).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3422 _ (by rfl)
    _ = 4521 := by rw [fixedPC3782]; rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3424 = 4522 := by
  calc
    Artifact.submissionArtifact.instructionPC 3424 =
        Artifact.submissionArtifact.instructionPC 3423 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3423 _ (by rfl)
    _ = 4522 := by rw [fixedPC3783]; rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3425 = 4525 := by
  calc
    Artifact.submissionArtifact.instructionPC 3425 =
        Artifact.submissionArtifact.instructionPC 3424 + (YulEvmCompiler.Instr.push 2 2688).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3424 _ (by rfl)
    _ = 4525 := by rw [fixedPC3784]; rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3426 = 4526 := by
  calc
    Artifact.submissionArtifact.instructionPC 3426 =
        Artifact.submissionArtifact.instructionPC 3425 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3425 _ (by rfl)
    _ = 4526 := by rw [fixedPC3785]; rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3427 = 4528 := by
  calc
    Artifact.submissionArtifact.instructionPC 3427 =
        Artifact.submissionArtifact.instructionPC 3426 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3426 _ (by rfl)
    _ = 4528 := by rw [fixedPC3786]; rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3428 = 4529 := by
  calc
    Artifact.submissionArtifact.instructionPC 3428 =
        Artifact.submissionArtifact.instructionPC 3427 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3427 _ (by rfl)
    _ = 4529 := by rw [fixedPC3787]; rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3429 = 4532 := by
  calc
    Artifact.submissionArtifact.instructionPC 3429 =
        Artifact.submissionArtifact.instructionPC 3428 + (YulEvmCompiler.Instr.push 2 4370).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3428 _ (by rfl)
    _ = 4532 := by rw [fixedPC3788]; rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3430 = 4533 := by
  calc
    Artifact.submissionArtifact.instructionPC 3430 =
        Artifact.submissionArtifact.instructionPC 3429 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3429 _ (by rfl)
    _ = 4533 := by rw [fixedPC3789]; rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3431 = 4536 := by
  calc
    Artifact.submissionArtifact.instructionPC 3431 =
        Artifact.submissionArtifact.instructionPC 3430 + (YulEvmCompiler.Instr.push 2 2784).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3430 _ (by rfl)
    _ = 4536 := by rw [fixedPC3790]; rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3432 = 4537 := by
  calc
    Artifact.submissionArtifact.instructionPC 3432 =
        Artifact.submissionArtifact.instructionPC 3431 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3431 _ (by rfl)
    _ = 4537 := by rw [fixedPC3791]; rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3433 = 4540 := by
  calc
    Artifact.submissionArtifact.instructionPC 3433 =
        Artifact.submissionArtifact.instructionPC 3432 + (YulEvmCompiler.Instr.push 2 2752).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3432 _ (by rfl)
    _ = 4540 := by rw [fixedPC3792]; rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3434 = 4541 := by
  calc
    Artifact.submissionArtifact.instructionPC 3434 =
        Artifact.submissionArtifact.instructionPC 3433 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3433 _ (by rfl)
    _ = 4541 := by rw [fixedPC3793]; rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3435 = 4542 := by
  calc
    Artifact.submissionArtifact.instructionPC 3435 =
        Artifact.submissionArtifact.instructionPC 3434 + (YulEvmCompiler.Instr.op (.Dup ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3434 _ (by rfl)
    _ = 4542 := by rw [fixedPC3794]; rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3436 = 4545 := by
  calc
    Artifact.submissionArtifact.instructionPC 3436 =
        Artifact.submissionArtifact.instructionPC 3435 + (YulEvmCompiler.Instr.push 2 1792).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3435 _ (by rfl)
    _ = 4545 := by rw [fixedPC3795]; rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3437 = 4546 := by
  calc
    Artifact.submissionArtifact.instructionPC 3437 =
        Artifact.submissionArtifact.instructionPC 3436 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3436 _ (by rfl)
    _ = 4546 := by rw [fixedPC3796]; rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3437 = 4546 := fixedPC3797

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3437 = 4546 := fixedPC3797

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3438 = 4547 := by
  calc
    Artifact.submissionArtifact.instructionPC 3438 =
        Artifact.submissionArtifact.instructionPC 3437 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3437 _ (by rfl)
    _ = 4547 := by rw [fixedPC3799]; rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3439 = 4548 := by
  calc
    Artifact.submissionArtifact.instructionPC 3439 =
        Artifact.submissionArtifact.instructionPC 3438 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3438 _ (by rfl)
    _ = 4548 := by rw [fixedPC3800]; rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3440 = 4549 := by
  calc
    Artifact.submissionArtifact.instructionPC 3440 =
        Artifact.submissionArtifact.instructionPC 3439 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3439 _ (by rfl)
    _ = 4549 := by rw [fixedPC3801]; rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3441 = 4552 := by
  calc
    Artifact.submissionArtifact.instructionPC 3441 =
        Artifact.submissionArtifact.instructionPC 3440 + (YulEvmCompiler.Instr.push 2 1566).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3440 _ (by rfl)
    _ = 4552 := by rw [fixedPC3802]; rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3442 = 4553 := by
  calc
    Artifact.submissionArtifact.instructionPC 3442 =
        Artifact.submissionArtifact.instructionPC 3441 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3441 _ (by rfl)
    _ = 4553 := by rw [fixedPC3803]; rfl

@[simp] theorem fixedJump5023 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4553 = true := by
  simpa only [Artifact.instructionPC, fixedPC3804] using Artifact.isValidJumpDest_index 3442 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3443 = 4554 := by
  calc
    Artifact.submissionArtifact.instructionPC 3443 =
        Artifact.submissionArtifact.instructionPC 3442 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3442 _ (by rfl)
    _ = 4554 := by rw [fixedPC3804]; rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3444 = 4557 := by
  calc
    Artifact.submissionArtifact.instructionPC 3444 =
        Artifact.submissionArtifact.instructionPC 3443 + (YulEvmCompiler.Instr.push 2 2336).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3443 _ (by rfl)
    _ = 4557 := by rw [fixedPC3805]; rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3445 = 4558 := by
  calc
    Artifact.submissionArtifact.instructionPC 3445 =
        Artifact.submissionArtifact.instructionPC 3444 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3444 _ (by rfl)
    _ = 4558 := by rw [fixedPC3806]; rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3446 = 4560 := by
  calc
    Artifact.submissionArtifact.instructionPC 3446 =
        Artifact.submissionArtifact.instructionPC 3445 + (YulEvmCompiler.Instr.push 1 224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3445 _ (by rfl)
    _ = 4560 := by rw [fixedPC3807]; rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3447 = 4561 := by
  calc
    Artifact.submissionArtifact.instructionPC 3447 =
        Artifact.submissionArtifact.instructionPC 3446 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3446 _ (by rfl)
    _ = 4561 := by rw [fixedPC3808]; rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3448 = 4562 := by
  calc
    Artifact.submissionArtifact.instructionPC 3448 =
        Artifact.submissionArtifact.instructionPC 3447 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3447 _ (by rfl)
    _ = 4562 := by rw [fixedPC3809]; rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3449 = 4563 := by
  calc
    Artifact.submissionArtifact.instructionPC 3449 =
        Artifact.submissionArtifact.instructionPC 3448 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3448 _ (by rfl)
    _ = 4563 := by rw [fixedPC3810]; rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3450 = 4564 := by
  calc
    Artifact.submissionArtifact.instructionPC 3450 =
        Artifact.submissionArtifact.instructionPC 3449 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3449 _ (by rfl)
    _ = 4564 := by rw [fixedPC3811]; rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3451 = 4565 := by
  calc
    Artifact.submissionArtifact.instructionPC 3451 =
        Artifact.submissionArtifact.instructionPC 3450 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3450 _ (by rfl)
    _ = 4565 := by rw [fixedPC3812]; rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3452 = 4566 := by
  calc
    Artifact.submissionArtifact.instructionPC 3452 =
        Artifact.submissionArtifact.instructionPC 3451 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3451 _ (by rfl)
    _ = 4566 := by rw [fixedPC3813]; rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3453 = 4569 := by
  calc
    Artifact.submissionArtifact.instructionPC 3453 =
        Artifact.submissionArtifact.instructionPC 3452 + (YulEvmCompiler.Instr.push 2 2016).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3452 _ (by rfl)
    _ = 4569 := by rw [fixedPC3814]; rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3454 = 4570 := by
  calc
    Artifact.submissionArtifact.instructionPC 3454 =
        Artifact.submissionArtifact.instructionPC 3453 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3453 _ (by rfl)
    _ = 4570 := by rw [fixedPC3815]; rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3455 = 4573 := by
  calc
    Artifact.submissionArtifact.instructionPC 3455 =
        Artifact.submissionArtifact.instructionPC 3454 + (YulEvmCompiler.Instr.push 2 2304).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3454 _ (by rfl)
    _ = 4573 := by rw [fixedPC3816]; rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3456 = 4574 := by
  calc
    Artifact.submissionArtifact.instructionPC 3456 =
        Artifact.submissionArtifact.instructionPC 3455 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3455 _ (by rfl)
    _ = 4574 := by rw [fixedPC3817]; rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3457 = 4576 := by
  calc
    Artifact.submissionArtifact.instructionPC 3457 =
        Artifact.submissionArtifact.instructionPC 3456 + (YulEvmCompiler.Instr.push 1 192).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3456 _ (by rfl)
    _ = 4576 := by rw [fixedPC3818]; rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3458 = 4577 := by
  calc
    Artifact.submissionArtifact.instructionPC 3458 =
        Artifact.submissionArtifact.instructionPC 3457 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3457 _ (by rfl)
    _ = 4577 := by rw [fixedPC3819]; rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3459 = 4578 := by
  calc
    Artifact.submissionArtifact.instructionPC 3459 =
        Artifact.submissionArtifact.instructionPC 3458 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3458 _ (by rfl)
    _ = 4578 := by rw [fixedPC3820]; rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3460 = 4579 := by
  calc
    Artifact.submissionArtifact.instructionPC 3460 =
        Artifact.submissionArtifact.instructionPC 3459 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3459 _ (by rfl)
    _ = 4579 := by rw [fixedPC3821]; rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3461 = 4580 := by
  calc
    Artifact.submissionArtifact.instructionPC 3461 =
        Artifact.submissionArtifact.instructionPC 3460 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3460 _ (by rfl)
    _ = 4580 := by rw [fixedPC3822]; rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3462 = 4581 := by
  calc
    Artifact.submissionArtifact.instructionPC 3462 =
        Artifact.submissionArtifact.instructionPC 3461 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3461 _ (by rfl)
    _ = 4581 := by rw [fixedPC3823]; rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3463 = 4582 := by
  calc
    Artifact.submissionArtifact.instructionPC 3463 =
        Artifact.submissionArtifact.instructionPC 3462 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3462 _ (by rfl)
    _ = 4582 := by rw [fixedPC3824]; rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3464 = 4583 := by
  calc
    Artifact.submissionArtifact.instructionPC 3464 =
        Artifact.submissionArtifact.instructionPC 3463 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3463 _ (by rfl)
    _ = 4583 := by rw [fixedPC3825]; rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3465 = 4584 := by
  calc
    Artifact.submissionArtifact.instructionPC 3465 =
        Artifact.submissionArtifact.instructionPC 3464 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3464 _ (by rfl)
    _ = 4584 := by rw [fixedPC3826]; rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3466 = 4585 := by
  calc
    Artifact.submissionArtifact.instructionPC 3466 =
        Artifact.submissionArtifact.instructionPC 3465 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3465 _ (by rfl)
    _ = 4585 := by rw [fixedPC3827]; rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3467 = 4586 := by
  calc
    Artifact.submissionArtifact.instructionPC 3467 =
        Artifact.submissionArtifact.instructionPC 3466 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3466 _ (by rfl)
    _ = 4586 := by rw [fixedPC3828]; rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3468 = 4587 := by
  calc
    Artifact.submissionArtifact.instructionPC 3468 =
        Artifact.submissionArtifact.instructionPC 3467 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3467 _ (by rfl)
    _ = 4587 := by rw [fixedPC3829]; rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3469 = 4588 := by
  calc
    Artifact.submissionArtifact.instructionPC 3469 =
        Artifact.submissionArtifact.instructionPC 3468 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3468 _ (by rfl)
    _ = 4588 := by rw [fixedPC3830]; rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3470 = 4589 := by
  calc
    Artifact.submissionArtifact.instructionPC 3470 =
        Artifact.submissionArtifact.instructionPC 3469 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3469 _ (by rfl)
    _ = 4589 := by rw [fixedPC3831]; rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3471 = 4592 := by
  calc
    Artifact.submissionArtifact.instructionPC 3471 =
        Artifact.submissionArtifact.instructionPC 3470 + (YulEvmCompiler.Instr.push 2 1984).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3470 _ (by rfl)
    _ = 4592 := by rw [fixedPC3832]; rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3472 = 4593 := by
  calc
    Artifact.submissionArtifact.instructionPC 3472 =
        Artifact.submissionArtifact.instructionPC 3471 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3471 _ (by rfl)
    _ = 4593 := by rw [fixedPC3833]; rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3473 = 4596 := by
  calc
    Artifact.submissionArtifact.instructionPC 3473 =
        Artifact.submissionArtifact.instructionPC 3472 + (YulEvmCompiler.Instr.push 2 2272).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3472 _ (by rfl)
    _ = 4596 := by rw [fixedPC3834]; rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3474 = 4597 := by
  calc
    Artifact.submissionArtifact.instructionPC 3474 =
        Artifact.submissionArtifact.instructionPC 3473 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3473 _ (by rfl)
    _ = 4597 := by rw [fixedPC3835]; rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3475 = 4599 := by
  calc
    Artifact.submissionArtifact.instructionPC 3475 =
        Artifact.submissionArtifact.instructionPC 3474 + (YulEvmCompiler.Instr.push 1 160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3474 _ (by rfl)
    _ = 4599 := by rw [fixedPC3836]; rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3476 = 4600 := by
  calc
    Artifact.submissionArtifact.instructionPC 3476 =
        Artifact.submissionArtifact.instructionPC 3475 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3475 _ (by rfl)
    _ = 4600 := by rw [fixedPC3837]; rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3477 = 4601 := by
  calc
    Artifact.submissionArtifact.instructionPC 3477 =
        Artifact.submissionArtifact.instructionPC 3476 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3476 _ (by rfl)
    _ = 4601 := by rw [fixedPC3838]; rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3478 = 4602 := by
  calc
    Artifact.submissionArtifact.instructionPC 3478 =
        Artifact.submissionArtifact.instructionPC 3477 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3477 _ (by rfl)
    _ = 4602 := by rw [fixedPC3839]; rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3479 = 4603 := by
  calc
    Artifact.submissionArtifact.instructionPC 3479 =
        Artifact.submissionArtifact.instructionPC 3478 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3478 _ (by rfl)
    _ = 4603 := by rw [fixedPC3840]; rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3480 = 4604 := by
  calc
    Artifact.submissionArtifact.instructionPC 3480 =
        Artifact.submissionArtifact.instructionPC 3479 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3479 _ (by rfl)
    _ = 4604 := by rw [fixedPC3841]; rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3481 = 4605 := by
  calc
    Artifact.submissionArtifact.instructionPC 3481 =
        Artifact.submissionArtifact.instructionPC 3480 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3480 _ (by rfl)
    _ = 4605 := by rw [fixedPC3842]; rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3482 = 4606 := by
  calc
    Artifact.submissionArtifact.instructionPC 3482 =
        Artifact.submissionArtifact.instructionPC 3481 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3481 _ (by rfl)
    _ = 4606 := by rw [fixedPC3843]; rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3483 = 4607 := by
  calc
    Artifact.submissionArtifact.instructionPC 3483 =
        Artifact.submissionArtifact.instructionPC 3482 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3482 _ (by rfl)
    _ = 4607 := by rw [fixedPC3844]; rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3484 = 4608 := by
  calc
    Artifact.submissionArtifact.instructionPC 3484 =
        Artifact.submissionArtifact.instructionPC 3483 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3483 _ (by rfl)
    _ = 4608 := by rw [fixedPC3845]; rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3485 = 4609 := by
  calc
    Artifact.submissionArtifact.instructionPC 3485 =
        Artifact.submissionArtifact.instructionPC 3484 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3484 _ (by rfl)
    _ = 4609 := by rw [fixedPC3846]; rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3486 = 4610 := by
  calc
    Artifact.submissionArtifact.instructionPC 3486 =
        Artifact.submissionArtifact.instructionPC 3485 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3485 _ (by rfl)
    _ = 4610 := by rw [fixedPC3847]; rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3487 = 4611 := by
  calc
    Artifact.submissionArtifact.instructionPC 3487 =
        Artifact.submissionArtifact.instructionPC 3486 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3486 _ (by rfl)
    _ = 4611 := by rw [fixedPC3848]; rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3488 = 4612 := by
  calc
    Artifact.submissionArtifact.instructionPC 3488 =
        Artifact.submissionArtifact.instructionPC 3487 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3487 _ (by rfl)
    _ = 4612 := by rw [fixedPC3849]; rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3489 = 4615 := by
  calc
    Artifact.submissionArtifact.instructionPC 3489 =
        Artifact.submissionArtifact.instructionPC 3488 + (YulEvmCompiler.Instr.push 2 1952).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3488 _ (by rfl)
    _ = 4615 := by rw [fixedPC3850]; rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3490 = 4616 := by
  calc
    Artifact.submissionArtifact.instructionPC 3490 =
        Artifact.submissionArtifact.instructionPC 3489 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3489 _ (by rfl)
    _ = 4616 := by rw [fixedPC3851]; rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3491 = 4619 := by
  calc
    Artifact.submissionArtifact.instructionPC 3491 =
        Artifact.submissionArtifact.instructionPC 3490 + (YulEvmCompiler.Instr.push 2 2240).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3490 _ (by rfl)
    _ = 4619 := by rw [fixedPC3852]; rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3492 = 4620 := by
  calc
    Artifact.submissionArtifact.instructionPC 3492 =
        Artifact.submissionArtifact.instructionPC 3491 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3491 _ (by rfl)
    _ = 4620 := by rw [fixedPC3853]; rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3493 = 4622 := by
  calc
    Artifact.submissionArtifact.instructionPC 3493 =
        Artifact.submissionArtifact.instructionPC 3492 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3492 _ (by rfl)
    _ = 4622 := by rw [fixedPC3854]; rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3494 = 4623 := by
  calc
    Artifact.submissionArtifact.instructionPC 3494 =
        Artifact.submissionArtifact.instructionPC 3493 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3493 _ (by rfl)
    _ = 4623 := by rw [fixedPC3855]; rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3495 = 4624 := by
  calc
    Artifact.submissionArtifact.instructionPC 3495 =
        Artifact.submissionArtifact.instructionPC 3494 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3494 _ (by rfl)
    _ = 4624 := by rw [fixedPC3856]; rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3496 = 4625 := by
  calc
    Artifact.submissionArtifact.instructionPC 3496 =
        Artifact.submissionArtifact.instructionPC 3495 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3495 _ (by rfl)
    _ = 4625 := by rw [fixedPC3857]; rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3497 = 4626 := by
  calc
    Artifact.submissionArtifact.instructionPC 3497 =
        Artifact.submissionArtifact.instructionPC 3496 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3496 _ (by rfl)
    _ = 4626 := by rw [fixedPC3858]; rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3498 = 4627 := by
  calc
    Artifact.submissionArtifact.instructionPC 3498 =
        Artifact.submissionArtifact.instructionPC 3497 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3497 _ (by rfl)
    _ = 4627 := by rw [fixedPC3859]; rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3499 = 4628 := by
  calc
    Artifact.submissionArtifact.instructionPC 3499 =
        Artifact.submissionArtifact.instructionPC 3498 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3498 _ (by rfl)
    _ = 4628 := by rw [fixedPC3860]; rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3500 = 4629 := by
  calc
    Artifact.submissionArtifact.instructionPC 3500 =
        Artifact.submissionArtifact.instructionPC 3499 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3499 _ (by rfl)
    _ = 4629 := by rw [fixedPC3861]; rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3501 = 4630 := by
  calc
    Artifact.submissionArtifact.instructionPC 3501 =
        Artifact.submissionArtifact.instructionPC 3500 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3500 _ (by rfl)
    _ = 4630 := by rw [fixedPC3862]; rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3502 = 4631 := by
  calc
    Artifact.submissionArtifact.instructionPC 3502 =
        Artifact.submissionArtifact.instructionPC 3501 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3501 _ (by rfl)
    _ = 4631 := by rw [fixedPC3863]; rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3503 = 4632 := by
  calc
    Artifact.submissionArtifact.instructionPC 3503 =
        Artifact.submissionArtifact.instructionPC 3502 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3502 _ (by rfl)
    _ = 4632 := by rw [fixedPC3864]; rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3504 = 4633 := by
  calc
    Artifact.submissionArtifact.instructionPC 3504 =
        Artifact.submissionArtifact.instructionPC 3503 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3503 _ (by rfl)
    _ = 4633 := by rw [fixedPC3865]; rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3505 = 4634 := by
  calc
    Artifact.submissionArtifact.instructionPC 3505 =
        Artifact.submissionArtifact.instructionPC 3504 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3504 _ (by rfl)
    _ = 4634 := by rw [fixedPC3866]; rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3506 = 4635 := by
  calc
    Artifact.submissionArtifact.instructionPC 3506 =
        Artifact.submissionArtifact.instructionPC 3505 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3505 _ (by rfl)
    _ = 4635 := by rw [fixedPC3867]; rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3507 = 4638 := by
  calc
    Artifact.submissionArtifact.instructionPC 3507 =
        Artifact.submissionArtifact.instructionPC 3506 + (YulEvmCompiler.Instr.push 2 1920).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3506 _ (by rfl)
    _ = 4638 := by rw [fixedPC3868]; rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3508 = 4639 := by
  calc
    Artifact.submissionArtifact.instructionPC 3508 =
        Artifact.submissionArtifact.instructionPC 3507 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3507 _ (by rfl)
    _ = 4639 := by rw [fixedPC3869]; rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3509 = 4642 := by
  calc
    Artifact.submissionArtifact.instructionPC 3509 =
        Artifact.submissionArtifact.instructionPC 3508 + (YulEvmCompiler.Instr.push 2 2208).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3508 _ (by rfl)
    _ = 4642 := by rw [fixedPC3871]; rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3510 = 4643 := by
  calc
    Artifact.submissionArtifact.instructionPC 3510 =
        Artifact.submissionArtifact.instructionPC 3509 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3509 _ (by rfl)
    _ = 4643 := by rw [fixedPC3872]; rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3511 = 4645 := by
  calc
    Artifact.submissionArtifact.instructionPC 3511 =
        Artifact.submissionArtifact.instructionPC 3510 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3510 _ (by rfl)
    _ = 4645 := by rw [fixedPC3873]; rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3512 = 4646 := by
  calc
    Artifact.submissionArtifact.instructionPC 3512 =
        Artifact.submissionArtifact.instructionPC 3511 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3511 _ (by rfl)
    _ = 4646 := by rw [fixedPC3874]; rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3513 = 4647 := by
  calc
    Artifact.submissionArtifact.instructionPC 3513 =
        Artifact.submissionArtifact.instructionPC 3512 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3512 _ (by rfl)
    _ = 4647 := by rw [fixedPC3875]; rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3514 = 4648 := by
  calc
    Artifact.submissionArtifact.instructionPC 3514 =
        Artifact.submissionArtifact.instructionPC 3513 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3513 _ (by rfl)
    _ = 4648 := by rw [fixedPC3876]; rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3515 = 4649 := by
  calc
    Artifact.submissionArtifact.instructionPC 3515 =
        Artifact.submissionArtifact.instructionPC 3514 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3514 _ (by rfl)
    _ = 4649 := by rw [fixedPC3877]; rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3516 = 4650 := by
  calc
    Artifact.submissionArtifact.instructionPC 3516 =
        Artifact.submissionArtifact.instructionPC 3515 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3515 _ (by rfl)
    _ = 4650 := by rw [fixedPC3878]; rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3517 = 4651 := by
  calc
    Artifact.submissionArtifact.instructionPC 3517 =
        Artifact.submissionArtifact.instructionPC 3516 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3516 _ (by rfl)
    _ = 4651 := by rw [fixedPC3879]; rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3518 = 4652 := by
  calc
    Artifact.submissionArtifact.instructionPC 3518 =
        Artifact.submissionArtifact.instructionPC 3517 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3517 _ (by rfl)
    _ = 4652 := by rw [fixedPC3880]; rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3519 = 4653 := by
  calc
    Artifact.submissionArtifact.instructionPC 3519 =
        Artifact.submissionArtifact.instructionPC 3518 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3518 _ (by rfl)
    _ = 4653 := by rw [fixedPC3881]; rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3520 = 4654 := by
  calc
    Artifact.submissionArtifact.instructionPC 3520 =
        Artifact.submissionArtifact.instructionPC 3519 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3519 _ (by rfl)
    _ = 4654 := by rw [fixedPC3882]; rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3521 = 4655 := by
  calc
    Artifact.submissionArtifact.instructionPC 3521 =
        Artifact.submissionArtifact.instructionPC 3520 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3520 _ (by rfl)
    _ = 4655 := by rw [fixedPC3883]; rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3522 = 4656 := by
  calc
    Artifact.submissionArtifact.instructionPC 3522 =
        Artifact.submissionArtifact.instructionPC 3521 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3521 _ (by rfl)
    _ = 4656 := by rw [fixedPC3884]; rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3523 = 4657 := by
  calc
    Artifact.submissionArtifact.instructionPC 3523 =
        Artifact.submissionArtifact.instructionPC 3522 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3522 _ (by rfl)
    _ = 4657 := by rw [fixedPC3885]; rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3524 = 4658 := by
  calc
    Artifact.submissionArtifact.instructionPC 3524 =
        Artifact.submissionArtifact.instructionPC 3523 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3523 _ (by rfl)
    _ = 4658 := by rw [fixedPC3886]; rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3525 = 4661 := by
  calc
    Artifact.submissionArtifact.instructionPC 3525 =
        Artifact.submissionArtifact.instructionPC 3524 + (YulEvmCompiler.Instr.push 2 1888).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3524 _ (by rfl)
    _ = 4661 := by rw [fixedPC3887]; rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3526 = 4662 := by
  calc
    Artifact.submissionArtifact.instructionPC 3526 =
        Artifact.submissionArtifact.instructionPC 3525 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3525 _ (by rfl)
    _ = 4662 := by rw [fixedPC3888]; rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4662 = true := by
  simpa only [Artifact.instructionPC, fixedPC3889] using Artifact.isValidJumpDest_index 3526 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3527 = 4663 := by
  calc
    Artifact.submissionArtifact.instructionPC 3527 =
        Artifact.submissionArtifact.instructionPC 3526 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3526 _ (by rfl)
    _ = 4663 := by rw [fixedPC3889]; rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3528 = 4666 := by
  calc
    Artifact.submissionArtifact.instructionPC 3528 =
        Artifact.submissionArtifact.instructionPC 3527 + (YulEvmCompiler.Instr.push 2 2176).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3527 _ (by rfl)
    _ = 4666 := by rw [fixedPC3890]; rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3529 = 4667 := by
  calc
    Artifact.submissionArtifact.instructionPC 3529 =
        Artifact.submissionArtifact.instructionPC 3528 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3528 _ (by rfl)
    _ = 4667 := by rw [fixedPC3891]; rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3530 = 4669 := by
  calc
    Artifact.submissionArtifact.instructionPC 3530 =
        Artifact.submissionArtifact.instructionPC 3529 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3529 _ (by rfl)
    _ = 4669 := by rw [fixedPC3892]; rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3531 = 4670 := by
  calc
    Artifact.submissionArtifact.instructionPC 3531 =
        Artifact.submissionArtifact.instructionPC 3530 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3530 _ (by rfl)
    _ = 4670 := by rw [fixedPC3893]; rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3532 = 4671 := by
  calc
    Artifact.submissionArtifact.instructionPC 3532 =
        Artifact.submissionArtifact.instructionPC 3531 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3531 _ (by rfl)
    _ = 4671 := by rw [fixedPC3894]; rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3533 = 4672 := by
  calc
    Artifact.submissionArtifact.instructionPC 3533 =
        Artifact.submissionArtifact.instructionPC 3532 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3532 _ (by rfl)
    _ = 4672 := by rw [fixedPC3895]; rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3534 = 4673 := by
  calc
    Artifact.submissionArtifact.instructionPC 3534 =
        Artifact.submissionArtifact.instructionPC 3533 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3533 _ (by rfl)
    _ = 4673 := by rw [fixedPC3896]; rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3535 = 4674 := by
  calc
    Artifact.submissionArtifact.instructionPC 3535 =
        Artifact.submissionArtifact.instructionPC 3534 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3534 _ (by rfl)
    _ = 4674 := by rw [fixedPC3897]; rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3536 = 4675 := by
  calc
    Artifact.submissionArtifact.instructionPC 3536 =
        Artifact.submissionArtifact.instructionPC 3535 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3535 _ (by rfl)
    _ = 4675 := by rw [fixedPC3898]; rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3537 = 4676 := by
  calc
    Artifact.submissionArtifact.instructionPC 3537 =
        Artifact.submissionArtifact.instructionPC 3536 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3536 _ (by rfl)
    _ = 4676 := by rw [fixedPC3899]; rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3538 = 4677 := by
  calc
    Artifact.submissionArtifact.instructionPC 3538 =
        Artifact.submissionArtifact.instructionPC 3537 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3537 _ (by rfl)
    _ = 4677 := by rw [fixedPC3900]; rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3539 = 4678 := by
  calc
    Artifact.submissionArtifact.instructionPC 3539 =
        Artifact.submissionArtifact.instructionPC 3538 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3538 _ (by rfl)
    _ = 4678 := by rw [fixedPC3901]; rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3540 = 4679 := by
  calc
    Artifact.submissionArtifact.instructionPC 3540 =
        Artifact.submissionArtifact.instructionPC 3539 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3539 _ (by rfl)
    _ = 4679 := by rw [fixedPC3902]; rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3541 = 4680 := by
  calc
    Artifact.submissionArtifact.instructionPC 3541 =
        Artifact.submissionArtifact.instructionPC 3540 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3540 _ (by rfl)
    _ = 4680 := by rw [fixedPC3903]; rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3542 = 4681 := by
  calc
    Artifact.submissionArtifact.instructionPC 3542 =
        Artifact.submissionArtifact.instructionPC 3541 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3541 _ (by rfl)
    _ = 4681 := by rw [fixedPC3904]; rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3543 = 4682 := by
  calc
    Artifact.submissionArtifact.instructionPC 3543 =
        Artifact.submissionArtifact.instructionPC 3542 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3542 _ (by rfl)
    _ = 4682 := by rw [fixedPC3905]; rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3544 = 4685 := by
  calc
    Artifact.submissionArtifact.instructionPC 3544 =
        Artifact.submissionArtifact.instructionPC 3543 + (YulEvmCompiler.Instr.push 2 1856).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3543 _ (by rfl)
    _ = 4685 := by rw [fixedPC3906]; rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3545 = 4686 := by
  calc
    Artifact.submissionArtifact.instructionPC 3545 =
        Artifact.submissionArtifact.instructionPC 3544 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3544 _ (by rfl)
    _ = 4686 := by rw [fixedPC3907]; rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3546 = 4689 := by
  calc
    Artifact.submissionArtifact.instructionPC 3546 =
        Artifact.submissionArtifact.instructionPC 3545 + (YulEvmCompiler.Instr.push 2 2144).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3545 _ (by rfl)
    _ = 4689 := by rw [fixedPC3908]; rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3547 = 4690 := by
  calc
    Artifact.submissionArtifact.instructionPC 3547 =
        Artifact.submissionArtifact.instructionPC 3546 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3546 _ (by rfl)
    _ = 4690 := by rw [fixedPC3909]; rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3548 = 4692 := by
  calc
    Artifact.submissionArtifact.instructionPC 3548 =
        Artifact.submissionArtifact.instructionPC 3547 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3547 _ (by rfl)
    _ = 4692 := by rw [fixedPC3910]; rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3549 = 4693 := by
  calc
    Artifact.submissionArtifact.instructionPC 3549 =
        Artifact.submissionArtifact.instructionPC 3548 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3548 _ (by rfl)
    _ = 4693 := by rw [fixedPC3911]; rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3550 = 4694 := by
  calc
    Artifact.submissionArtifact.instructionPC 3550 =
        Artifact.submissionArtifact.instructionPC 3549 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3549 _ (by rfl)
    _ = 4694 := by rw [fixedPC3912]; rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3551 = 4695 := by
  calc
    Artifact.submissionArtifact.instructionPC 3551 =
        Artifact.submissionArtifact.instructionPC 3550 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3550 _ (by rfl)
    _ = 4695 := by rw [fixedPC3913]; rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3552 = 4696 := by
  calc
    Artifact.submissionArtifact.instructionPC 3552 =
        Artifact.submissionArtifact.instructionPC 3551 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3551 _ (by rfl)
    _ = 4696 := by rw [fixedPC3914]; rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3553 = 4697 := by
  calc
    Artifact.submissionArtifact.instructionPC 3553 =
        Artifact.submissionArtifact.instructionPC 3552 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3552 _ (by rfl)
    _ = 4697 := by rw [fixedPC3915]; rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3554 = 4698 := by
  calc
    Artifact.submissionArtifact.instructionPC 3554 =
        Artifact.submissionArtifact.instructionPC 3553 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3553 _ (by rfl)
    _ = 4698 := by rw [fixedPC3916]; rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3555 = 4699 := by
  calc
    Artifact.submissionArtifact.instructionPC 3555 =
        Artifact.submissionArtifact.instructionPC 3554 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3554 _ (by rfl)
    _ = 4699 := by rw [fixedPC3917]; rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3556 = 4700 := by
  calc
    Artifact.submissionArtifact.instructionPC 3556 =
        Artifact.submissionArtifact.instructionPC 3555 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3555 _ (by rfl)
    _ = 4700 := by rw [fixedPC3918]; rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3557 = 4701 := by
  calc
    Artifact.submissionArtifact.instructionPC 3557 =
        Artifact.submissionArtifact.instructionPC 3556 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3556 _ (by rfl)
    _ = 4701 := by rw [fixedPC3919]; rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3558 = 4702 := by
  calc
    Artifact.submissionArtifact.instructionPC 3558 =
        Artifact.submissionArtifact.instructionPC 3557 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3557 _ (by rfl)
    _ = 4702 := by rw [fixedPC3920]; rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3559 = 4703 := by
  calc
    Artifact.submissionArtifact.instructionPC 3559 =
        Artifact.submissionArtifact.instructionPC 3558 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3558 _ (by rfl)
    _ = 4703 := by rw [fixedPC3921]; rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3560 = 4704 := by
  calc
    Artifact.submissionArtifact.instructionPC 3560 =
        Artifact.submissionArtifact.instructionPC 3559 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3559 _ (by rfl)
    _ = 4704 := by rw [fixedPC3922]; rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3561 = 4705 := by
  calc
    Artifact.submissionArtifact.instructionPC 3561 =
        Artifact.submissionArtifact.instructionPC 3560 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3560 _ (by rfl)
    _ = 4705 := by rw [fixedPC3923]; rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3562 = 4708 := by
  calc
    Artifact.submissionArtifact.instructionPC 3562 =
        Artifact.submissionArtifact.instructionPC 3561 + (YulEvmCompiler.Instr.push 2 1824).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3561 _ (by rfl)
    _ = 4708 := by rw [fixedPC3924]; rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3563 = 4709 := by
  calc
    Artifact.submissionArtifact.instructionPC 3563 =
        Artifact.submissionArtifact.instructionPC 3562 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3562 _ (by rfl)
    _ = 4709 := by rw [fixedPC3925]; rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3564 = 4712 := by
  calc
    Artifact.submissionArtifact.instructionPC 3564 =
        Artifact.submissionArtifact.instructionPC 3563 + (YulEvmCompiler.Instr.push 2 2112).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3563 _ (by rfl)
    _ = 4712 := by rw [fixedPC3926]; rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3565 = 4713 := by
  calc
    Artifact.submissionArtifact.instructionPC 3565 =
        Artifact.submissionArtifact.instructionPC 3564 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3564 _ (by rfl)
    _ = 4713 := by rw [fixedPC3927]; rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3566 = 4714 := by
  calc
    Artifact.submissionArtifact.instructionPC 3566 =
        Artifact.submissionArtifact.instructionPC 3565 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3565 _ (by rfl)
    _ = 4714 := by rw [fixedPC3928]; rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3567 = 4715 := by
  calc
    Artifact.submissionArtifact.instructionPC 3567 =
        Artifact.submissionArtifact.instructionPC 3566 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3566 _ (by rfl)
    _ = 4715 := by rw [fixedPC3929]; rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3568 = 4716 := by
  calc
    Artifact.submissionArtifact.instructionPC 3568 =
        Artifact.submissionArtifact.instructionPC 3567 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3567 _ (by rfl)
    _ = 4716 := by rw [fixedPC3930]; rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3569 = 4717 := by
  calc
    Artifact.submissionArtifact.instructionPC 3569 =
        Artifact.submissionArtifact.instructionPC 3568 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3568 _ (by rfl)
    _ = 4717 := by rw [fixedPC3931]; rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3570 = 4718 := by
  calc
    Artifact.submissionArtifact.instructionPC 3570 =
        Artifact.submissionArtifact.instructionPC 3569 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3569 _ (by rfl)
    _ = 4718 := by rw [fixedPC3932]; rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3571 = 4719 := by
  calc
    Artifact.submissionArtifact.instructionPC 3571 =
        Artifact.submissionArtifact.instructionPC 3570 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3570 _ (by rfl)
    _ = 4719 := by rw [fixedPC3933]; rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3572 = 4720 := by
  calc
    Artifact.submissionArtifact.instructionPC 3572 =
        Artifact.submissionArtifact.instructionPC 3571 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3571 _ (by rfl)
    _ = 4720 := by rw [fixedPC3934]; rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3573 = 4721 := by
  calc
    Artifact.submissionArtifact.instructionPC 3573 =
        Artifact.submissionArtifact.instructionPC 3572 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3572 _ (by rfl)
    _ = 4721 := by rw [fixedPC3935]; rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3574 = 4722 := by
  calc
    Artifact.submissionArtifact.instructionPC 3574 =
        Artifact.submissionArtifact.instructionPC 3573 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3573 _ (by rfl)
    _ = 4722 := by rw [fixedPC3936]; rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3575 = 4723 := by
  calc
    Artifact.submissionArtifact.instructionPC 3575 =
        Artifact.submissionArtifact.instructionPC 3574 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3574 _ (by rfl)
    _ = 4723 := by rw [fixedPC3937]; rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3576 = 4724 := by
  calc
    Artifact.submissionArtifact.instructionPC 3576 =
        Artifact.submissionArtifact.instructionPC 3575 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3575 _ (by rfl)
    _ = 4724 := by rw [fixedPC3938]; rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3577 = 4725 := by
  calc
    Artifact.submissionArtifact.instructionPC 3577 =
        Artifact.submissionArtifact.instructionPC 3576 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3576 _ (by rfl)
    _ = 4725 := by rw [fixedPC3939]; rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3578 = 4726 := by
  calc
    Artifact.submissionArtifact.instructionPC 3578 =
        Artifact.submissionArtifact.instructionPC 3577 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3577 _ (by rfl)
    _ = 4726 := by rw [fixedPC3940]; rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3579 = 4727 := by
  calc
    Artifact.submissionArtifact.instructionPC 3579 =
        Artifact.submissionArtifact.instructionPC 3578 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3578 _ (by rfl)
    _ = 4727 := by rw [fixedPC3941]; rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3580 = 4730 := by
  calc
    Artifact.submissionArtifact.instructionPC 3580 =
        Artifact.submissionArtifact.instructionPC 3579 + (YulEvmCompiler.Instr.push 2 1792).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3579 _ (by rfl)
    _ = 4730 := by rw [fixedPC3942]; rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3581 = 4731 := by
  calc
    Artifact.submissionArtifact.instructionPC 3581 =
        Artifact.submissionArtifact.instructionPC 3580 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3580 _ (by rfl)
    _ = 4731 := by rw [fixedPC3943]; rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3582 = 4732 := by
  calc
    Artifact.submissionArtifact.instructionPC 3582 =
        Artifact.submissionArtifact.instructionPC 3581 + (YulEvmCompiler.Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3581 _ (by rfl)
    _ = 4732 := by rw [fixedPC3944]; rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3583 = 4735 := by
  calc
    Artifact.submissionArtifact.instructionPC 3583 =
        Artifact.submissionArtifact.instructionPC 3582 + (YulEvmCompiler.Instr.push 2 2080).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3582 _ (by rfl)
    _ = 4735 := by rw [fixedPC3945]; rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3584 = 4736 := by
  calc
    Artifact.submissionArtifact.instructionPC 3584 =
        Artifact.submissionArtifact.instructionPC 3583 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3583 _ (by rfl)
    _ = 4736 := by rw [fixedPC3946]; rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3585 = 4737 := by
  calc
    Artifact.submissionArtifact.instructionPC 3585 =
        Artifact.submissionArtifact.instructionPC 3584 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3584 _ (by rfl)
    _ = 4737 := by rw [fixedPC3947]; rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3597 = 4757 := by
  decide

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3597 = 4757 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3598 = 4758 := by
  calc
    Artifact.submissionArtifact.instructionPC 3598 =
        Artifact.submissionArtifact.instructionPC 3597 + (YulEvmCompiler.Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3597 _ (by rfl)
    _ = 4758 := by rw [fixedPC3950]; rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3599 = 4761 := by
  calc
    Artifact.submissionArtifact.instructionPC 3599 =
        Artifact.submissionArtifact.instructionPC 3598 + (YulEvmCompiler.Instr.push 2 2112).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3598 _ (by rfl)
    _ = 4761 := by rw [fixedPC3951]; rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3600 = 4762 := by
  calc
    Artifact.submissionArtifact.instructionPC 3600 =
        Artifact.submissionArtifact.instructionPC 3599 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3599 _ (by rfl)
    _ = 4762 := by rw [fixedPC3952]; rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3601 = 4765 := by
  calc
    Artifact.submissionArtifact.instructionPC 3601 =
        Artifact.submissionArtifact.instructionPC 3600 + (YulEvmCompiler.Instr.push 2 2688).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3600 _ (by rfl)
    _ = 4765 := by rw [fixedPC3953]; rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3602 = 4766 := by
  calc
    Artifact.submissionArtifact.instructionPC 3602 =
        Artifact.submissionArtifact.instructionPC 3601 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3601 _ (by rfl)
    _ = 4766 := by rw [fixedPC3954]; rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3603 = 4767 := by
  calc
    Artifact.submissionArtifact.instructionPC 3603 =
        Artifact.submissionArtifact.instructionPC 3602 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3602 _ (by rfl)
    _ = 4767 := by rw [fixedPC3955]; rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3604 = 4768 := by
  calc
    Artifact.submissionArtifact.instructionPC 3604 =
        Artifact.submissionArtifact.instructionPC 3603 + (YulEvmCompiler.Instr.op .MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3603 _ (by rfl)
    _ = 4768 := by rw [fixedPC3956]; rfl

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

@[simp] theorem fixedPC3977 : Artifact.submissionArtifact.instructionPC 18 = 24 := by rfl

@[simp] theorem fixedPC3978 : Artifact.submissionArtifact.instructionPC 19 = 25 := by
  calc
    Artifact.submissionArtifact.instructionPC 19 =
        Artifact.submissionArtifact.instructionPC 18 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 18 _ (by rfl)
    _ = 25 := by rw [fixedPC3977]; rfl

@[simp] theorem fixedPC3979 : Artifact.submissionArtifact.instructionPC 20 = 26 := by
  calc
    Artifact.submissionArtifact.instructionPC 20 =
        Artifact.submissionArtifact.instructionPC 19 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 19 _ (by rfl)
    _ = 26 := by rw [fixedPC3978]; rfl

@[simp] theorem fixedPC3980 : Artifact.submissionArtifact.instructionPC 21 = 28 := by
  calc
    Artifact.submissionArtifact.instructionPC 21 =
        Artifact.submissionArtifact.instructionPC 20 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 20 _ (by rfl)
    _ = 28 := by rw [fixedPC3979]; rfl

@[simp] theorem fixedPC3981 : Artifact.submissionArtifact.instructionPC 22 = 29 := by
  calc
    Artifact.submissionArtifact.instructionPC 22 =
        Artifact.submissionArtifact.instructionPC 21 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 21 _ (by rfl)
    _ = 29 := by rw [fixedPC3980]; rfl

@[simp] theorem fixedPC3982 : Artifact.submissionArtifact.instructionPC 23 = 30 := by
  calc
    Artifact.submissionArtifact.instructionPC 23 =
        Artifact.submissionArtifact.instructionPC 22 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 22 _ (by rfl)
    _ = 30 := by rw [fixedPC3981]; rfl

@[simp] theorem fixedPC3983 : Artifact.submissionArtifact.instructionPC 24 = 31 := by
  calc
    Artifact.submissionArtifact.instructionPC 24 =
        Artifact.submissionArtifact.instructionPC 23 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 23 _ (by rfl)
    _ = 31 := by rw [fixedPC3982]; rfl

@[simp] theorem fixedPC3984 : Artifact.submissionArtifact.instructionPC 25 = 32 := by
  calc
    Artifact.submissionArtifact.instructionPC 25 =
        Artifact.submissionArtifact.instructionPC 24 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 24 _ (by rfl)
    _ = 32 := by rw [fixedPC3983]; rfl

@[simp] theorem fixedPC3985 : Artifact.submissionArtifact.instructionPC 26 = 35 := by
  calc
    Artifact.submissionArtifact.instructionPC 26 =
        Artifact.submissionArtifact.instructionPC 25 + (YulEvmCompiler.Instr.push 2 1186).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 25 _ (by rfl)
    _ = 35 := by rw [fixedPC3984]; rfl

@[simp] theorem fixedPC3986 : Artifact.submissionArtifact.instructionPC 27 = 36 := by
  calc
    Artifact.submissionArtifact.instructionPC 27 =
        Artifact.submissionArtifact.instructionPC 26 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 26 _ (by rfl)
    _ = 36 := by rw [fixedPC3985]; rfl

@[simp] theorem fixedPC3987 : Artifact.submissionArtifact.instructionPC 28 = 37 := by
  calc
    Artifact.submissionArtifact.instructionPC 28 =
        Artifact.submissionArtifact.instructionPC 27 + (YulEvmCompiler.Instr.op (.Dup ⟨3, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 27 _ (by rfl)
    _ = 37 := by rw [fixedPC3986]; rfl

@[simp] theorem fixedPC3988 : Artifact.submissionArtifact.instructionPC 29 = 39 := by
  calc
    Artifact.submissionArtifact.instructionPC 29 =
        Artifact.submissionArtifact.instructionPC 28 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 28 _ (by rfl)
    _ = 39 := by rw [fixedPC3987]; rfl

@[simp] theorem fixedPC3989 : Artifact.submissionArtifact.instructionPC 30 = 40 := by
  calc
    Artifact.submissionArtifact.instructionPC 30 =
        Artifact.submissionArtifact.instructionPC 29 + (YulEvmCompiler.Instr.op (.Dup ⟨6, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 29 _ (by rfl)
    _ = 40 := by rw [fixedPC3988]; rfl

@[simp] theorem fixedPC3990 : Artifact.submissionArtifact.instructionPC 31 = 41 := by
  calc
    Artifact.submissionArtifact.instructionPC 31 =
        Artifact.submissionArtifact.instructionPC 30 + (YulEvmCompiler.Instr.op (.Dup ⟨8, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 30 _ (by rfl)
    _ = 41 := by rw [fixedPC3989]; rfl

@[simp] theorem fixedPC3991 : Artifact.submissionArtifact.instructionPC 32 = 42 := by
  calc
    Artifact.submissionArtifact.instructionPC 32 =
        Artifact.submissionArtifact.instructionPC 31 + (YulEvmCompiler.Instr.op (.Dup ⟨10, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 31 _ (by rfl)
    _ = 42 := by rw [fixedPC3990]; rfl

@[simp] theorem fixedPC3992 : Artifact.submissionArtifact.instructionPC 32 = 42 := by rfl

@[simp] theorem fixedPC3993 : Artifact.submissionArtifact.instructionPC 70 = 125 := by rfl

@[simp] theorem fixedJump5272 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 125 = true := by
  simpa only [Artifact.instructionPC, fixedPC3993] using Artifact.isValidJumpDest_index 70 (by rfl)

@[simp] theorem fixedPC3994 : Artifact.submissionArtifact.instructionPC 71 = 126 := by
  calc
    Artifact.submissionArtifact.instructionPC 71 =
        Artifact.submissionArtifact.instructionPC 70 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 70 _ (by rfl)
    _ = 126 := by rw [fixedPC3993]; rfl

@[simp] theorem fixedPC3995 : Artifact.submissionArtifact.instructionPC 72 = 127 := by
  calc
    Artifact.submissionArtifact.instructionPC 72 =
        Artifact.submissionArtifact.instructionPC 71 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 71 _ (by rfl)
    _ = 127 := by rw [fixedPC3994]; rfl

@[simp] theorem fixedPC3996 : Artifact.submissionArtifact.instructionPC 73 = 128 := by
  calc
    Artifact.submissionArtifact.instructionPC 73 =
        Artifact.submissionArtifact.instructionPC 72 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 72 _ (by rfl)
    _ = 128 := by rw [fixedPC3995]; rfl

@[simp] theorem fixedPC3997 : Artifact.submissionArtifact.instructionPC 74 = 129 := by
  calc
    Artifact.submissionArtifact.instructionPC 74 =
        Artifact.submissionArtifact.instructionPC 73 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 73 _ (by rfl)
    _ = 129 := by rw [fixedPC3996]; rfl

@[simp] theorem fixedPC3998 : Artifact.submissionArtifact.instructionPC 75 = 132 := by
  calc
    Artifact.submissionArtifact.instructionPC 75 =
        Artifact.submissionArtifact.instructionPC 74 + (YulEvmCompiler.Instr.push 2 709).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 74 _ (by rfl)
    _ = 132 := by rw [fixedPC3997]; rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3315 = 4370 := by
  decide

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4370 = true := by
  simpa only [Artifact.instructionPC, fixedPC3999] using Artifact.isValidJumpDest_index 3315 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3316 = 4371 := by
  calc
    Artifact.submissionArtifact.instructionPC 3316 =
        Artifact.submissionArtifact.instructionPC 3315 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3315 _ (by rfl)
    _ = 4371 := by rw [fixedPC3999]; rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3317 = 4374 := by
  calc
    Artifact.submissionArtifact.instructionPC 3317 =
        Artifact.submissionArtifact.instructionPC 3316 + (YulEvmCompiler.Instr.push 2 2208).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3316 _ (by rfl)
    _ = 4374 := by rw [fixedPC4000]; rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3318 = 4375 := by
  calc
    Artifact.submissionArtifact.instructionPC 3318 =
        Artifact.submissionArtifact.instructionPC 3317 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3317 _ (by rfl)
    _ = 4375 := by rw [fixedPC4001]; rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3319 = 4377 := by
  calc
    Artifact.submissionArtifact.instructionPC 3319 =
        Artifact.submissionArtifact.instructionPC 3318 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3318 _ (by rfl)
    _ = 4377 := by rw [fixedPC4002]; rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3320 = 4378 := by
  calc
    Artifact.submissionArtifact.instructionPC 3320 =
        Artifact.submissionArtifact.instructionPC 3319 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3319 _ (by rfl)
    _ = 4378 := by rw [fixedPC4003]; rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3321 = 4379 := by
  calc
    Artifact.submissionArtifact.instructionPC 3321 =
        Artifact.submissionArtifact.instructionPC 3320 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3320 _ (by rfl)
    _ = 4379 := by rw [fixedPC4004]; rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3322 = 4380 := by
  calc
    Artifact.submissionArtifact.instructionPC 3322 =
        Artifact.submissionArtifact.instructionPC 3321 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3321 _ (by rfl)
    _ = 4380 := by rw [fixedPC4005]; rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3323 = 4381 := by
  calc
    Artifact.submissionArtifact.instructionPC 3323 =
        Artifact.submissionArtifact.instructionPC 3322 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3322 _ (by rfl)
    _ = 4381 := by rw [fixedPC4006]; rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3324 = 4382 := by
  calc
    Artifact.submissionArtifact.instructionPC 3324 =
        Artifact.submissionArtifact.instructionPC 3323 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3323 _ (by rfl)
    _ = 4382 := by rw [fixedPC4007]; rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3325 = 4383 := by
  calc
    Artifact.submissionArtifact.instructionPC 3325 =
        Artifact.submissionArtifact.instructionPC 3324 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3324 _ (by rfl)
    _ = 4383 := by rw [fixedPC4008]; rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3326 = 4386 := by
  calc
    Artifact.submissionArtifact.instructionPC 3326 =
        Artifact.submissionArtifact.instructionPC 3325 + (YulEvmCompiler.Instr.push 2 1888).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3325 _ (by rfl)
    _ = 4386 := by rw [fixedPC4009]; rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3327 = 4387 := by
  calc
    Artifact.submissionArtifact.instructionPC 3327 =
        Artifact.submissionArtifact.instructionPC 3326 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3326 _ (by rfl)
    _ = 4387 := by rw [fixedPC4010]; rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3328 = 4390 := by
  calc
    Artifact.submissionArtifact.instructionPC 3328 =
        Artifact.submissionArtifact.instructionPC 3327 + (YulEvmCompiler.Instr.push 2 4662).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3327 _ (by rfl)
    _ = 4390 := by rw [fixedPC4011]; rfl


@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2495 = 3314 := by rfl
@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3302 = 4349 := by rfl
@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3303 = 4350 := by rfl
@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3304 = 4351 := by rfl
@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3305 = 4352 := by rfl
@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3306 = 4355 := by rfl
@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3307 = 4356 := by rfl
@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3308 = 4357 := by rfl
@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3309 = 4360 := by rfl
@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3310 = 4361 := by rfl
@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3311 = 4362 := by rfl
@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3311 = 4362 := by rfl
@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3312 = 4365 := by rfl
@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3313 = 4366 := by rfl
@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3314 = 4369 := by rfl
@[simp] theorem earlyExtraPC2927 : Artifact.submissionArtifact.instructionPC 2495 = 3314 := by rfl
@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3315 = 4370 := by rfl
@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3316 = 4371 := by rfl
@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3317 = 4374 := by rfl
@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3318 = 4375 := by rfl
@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3319 = 4377 := by rfl
@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3320 = 4378 := by rfl
@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3321 = 4379 := by rfl
@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3322 = 4380 := by rfl
@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3323 = 4381 := by rfl
@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3324 = 4382 := by rfl
@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3325 = 4383 := by rfl
@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3326 = 4386 := by rfl
@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3327 = 4387 := by rfl
@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3328 = 4390 := by rfl
@[simp] theorem earlyExtraPC3918 : Artifact.submissionArtifact.instructionPC 3586 = 4740 := by rfl
@[simp] theorem earlyExtraPC3919 : Artifact.submissionArtifact.instructionPC 3587 = 4741 := by rfl
@[simp] theorem earlyExtraPC3920 : Artifact.submissionArtifact.instructionPC 3588 = 4744 := by rfl
@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 3589 = 4745 := by rfl
@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 3590 = 4746 := by rfl
@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 3591 = 4749 := by rfl
@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 3592 = 4752 := by rfl
@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 3593 = 4753 := by rfl
@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 3594 = 4754 := by rfl
@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 3595 = 4755 := by rfl
@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 3596 = 4756 := by rfl
end Challenge.Modexp.Submission.Proofs.Fast
