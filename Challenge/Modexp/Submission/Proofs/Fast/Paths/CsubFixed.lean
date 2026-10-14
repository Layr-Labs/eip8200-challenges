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
  [opAt 3383 .JUMPDEST,
   pushAt 3384 2 2688,
   opAt 3385 .MLOAD,
   pushAt 3386 1 128,
   opAt 3387 .EQ,
   pushAt 3388 2 4156,
   opAt 3389 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3383 .JUMPDEST,
   pushAt 3384 2 2688,
   opAt 3385 .MLOAD,
   pushAt 3386 1 128,
   opAt 3387 .EQ,
   pushAt 3388 2 4156,
   opAt 3389 .JUMPI,
   opAt 3271 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3390 .JUMPDEST,
   pushAt 3391 2 2336,
   opAt 3392 .MLOAD,
   pushAt 3393 1 224,
   opAt 3394 .MLOAD,
   opAt 3395 (.Dup ⟨0, by decide⟩),
   opAt 3396 (.Dup ⟨2, by decide⟩),
   opAt 3397 .SUB,
   pushAt 3398 2 2016,
   opAt 3399 .MSTORE,
   opAt 3400 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3401 (.Dup ⟨0, by decide⟩),
   pushAt 3402 1 192,
   opAt 3403 .MLOAD,
   opAt 3404 .ADD,
   opAt 3405 (.Dup ⟨0, by decide⟩),
   pushAt 3406 2 2304,
   opAt 3407 .MLOAD,
   opAt 3408 (.Dup ⟨1, by decide⟩),
   opAt 3409 (.Dup ⟨1, by decide⟩),
   opAt 3410 .SUB,
   pushAt 3411 2 1984,
   opAt 3412 .MSTORE,
   opAt 3413 .LT,
   opAt 3414 (.Swap ⟨1, by decide⟩),
   opAt 3415 .GT,
   opAt 3416 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3417 (.Dup ⟨0, by decide⟩),
   pushAt 3418 1 160,
   opAt 3419 .MLOAD,
   opAt 3420 .ADD,
   opAt 3421 (.Dup ⟨0, by decide⟩),
   pushAt 3422 2 2272,
   opAt 3423 .MLOAD,
   opAt 3424 (.Dup ⟨1, by decide⟩),
   opAt 3425 (.Dup ⟨1, by decide⟩),
   opAt 3426 .SUB,
   pushAt 3427 2 1952,
   opAt 3428 .MSTORE,
   opAt 3429 .LT,
   opAt 3430 (.Swap ⟨1, by decide⟩),
   opAt 3431 .GT,
   opAt 3432 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3433 (.Dup ⟨0, by decide⟩),
   pushAt 3434 1 128,
   opAt 3435 .MLOAD,
   opAt 3436 .ADD,
   opAt 3437 (.Dup ⟨0, by decide⟩),
   pushAt 3438 2 2240,
   opAt 3439 .MLOAD,
   opAt 3440 (.Dup ⟨1, by decide⟩),
   opAt 3441 (.Dup ⟨1, by decide⟩),
   opAt 3442 .SUB,
   pushAt 3443 2 1920,
   opAt 3444 .MSTORE,
   opAt 3445 .LT,
   opAt 3446 (.Swap ⟨1, by decide⟩),
   opAt 3447 .GT,
   opAt 3448 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3449 (.Dup ⟨0, by decide⟩),
   pushAt 3450 1 96,
   opAt 3451 .MLOAD,
   opAt 3452 .ADD,
   opAt 3453 (.Dup ⟨0, by decide⟩),
   pushAt 3454 2 2208,
   opAt 3455 .MLOAD,
   opAt 3456 (.Dup ⟨1, by decide⟩),
   opAt 3457 (.Dup ⟨1, by decide⟩),
   opAt 3458 .SUB,
   pushAt 3459 2 1888,
   opAt 3460 .MSTORE,
   opAt 3461 .LT,
   opAt 3462 (.Swap ⟨1, by decide⟩),
   opAt 3463 .GT,
   opAt 3464 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3465 .JUMPDEST,
   opAt 3466 (.Dup ⟨0, by decide⟩),
   pushAt 3467 1 64,
   opAt 3468 .MLOAD,
   opAt 3469 .ADD,
   opAt 3470 (.Dup ⟨0, by decide⟩),
   pushAt 3471 2 2176,
   opAt 3472 .MLOAD,
   opAt 3473 (.Dup ⟨1, by decide⟩),
   opAt 3474 (.Dup ⟨1, by decide⟩),
   opAt 3475 .SUB,
   pushAt 3476 2 1856,
   opAt 3477 .MSTORE,
   opAt 3478 .LT,
   opAt 3479 (.Swap ⟨1, by decide⟩),
   opAt 3480 .GT,
   opAt 3481 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3482 (.Dup ⟨0, by decide⟩),
   pushAt 3483 1 32,
   opAt 3484 .MLOAD,
   opAt 3485 .ADD,
   opAt 3486 (.Dup ⟨0, by decide⟩),
   pushAt 3487 2 2144,
   opAt 3488 .MLOAD,
   opAt 3489 (.Dup ⟨1, by decide⟩),
   opAt 3490 (.Dup ⟨1, by decide⟩),
   opAt 3491 .SUB,
   pushAt 3492 2 1824,
   opAt 3493 .MSTORE,
   opAt 3494 .LT,
   opAt 3495 (.Swap ⟨1, by decide⟩),
   opAt 3496 .GT,
   opAt 3497 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3498 (.Dup ⟨0, by decide⟩),
   pushAt 3499 0 0,
   opAt 3500 .MLOAD,
   opAt 3501 .ADD,
   opAt 3502 (.Dup ⟨0, by decide⟩),
   pushAt 3503 2 2112,
   opAt 3504 .MLOAD,
   opAt 3505 (.Dup ⟨1, by decide⟩),
   opAt 3506 (.Dup ⟨1, by decide⟩),
   opAt 3507 .SUB,
   pushAt 3508 2 1792,
   opAt 3509 .MSTORE,
   opAt 3510 .LT,
   opAt 3511 (.Swap ⟨1, by decide⟩),
   opAt 3512 .GT,
   opAt 3513 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3514 .ISZERO,
   pushAt 3515 2 2080,
   opAt 3516 .MLOAD,
   opAt 3517 .OR,
   pushAt 3518 2 4523,
   opAt 3519 .JUMPI,
   opAt 3534 .JUMPDEST,
   pushAt 3535 2 1792,
   pushAt 3536 2 2688,
   opAt 3537 .MLOAD,
   opAt 3538 (.Swap ⟨1, by decide⟩),
   opAt 3539 .MCOPY,
   opAt 3540 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3514 .ISZERO,
   pushAt 3515 2 2080,
   opAt 3516 .MLOAD,
   opAt 3517 .OR,
   pushAt 3518 2 4523,
   opAt 3519 .JUMPI,
   pushAt 3520 2 4512,
   opAt 3521 .JUMP,
   opAt 3527 .JUMPDEST,
   pushAt 3528 2 2112,
   pushAt 3529 2 2688,
   opAt 3530 .MLOAD,
   opAt 3531 (.Swap ⟨1, by decide⟩),
   opAt 3532 .MCOPY,
   opAt 3533 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3272 2 2208,
   opAt 3273 .MLOAD,
   pushAt 3274 1 96,
   opAt 3275 .MLOAD,
   opAt 3276 (.Dup ⟨0, by decide⟩),
   opAt 3277 (.Dup ⟨2, by decide⟩),
   opAt 3278 .SUB,
   pushAt 3279 2 1888,
   opAt 3280 .MSTORE,
   opAt 3281 .GT,
   pushAt 3282 2 4426,
   opAt 3283 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3465 .JUMPDEST,
   opAt 3466 (.Dup ⟨0, by decide⟩),
   pushAt 3467 1 64,
   opAt 3468 .MLOAD,
   opAt 3469 .ADD,
   opAt 3470 (.Dup ⟨0, by decide⟩),
   pushAt 3471 2 2176,
   opAt 3472 .MLOAD,
   opAt 3473 (.Dup ⟨1, by decide⟩),
   opAt 3474 (.Dup ⟨1, by decide⟩),
   opAt 3475 .SUB,
   pushAt 3476 2 1856,
   opAt 3477 .MSTORE,
   opAt 3478 .LT,
   opAt 3479 (.Swap ⟨1, by decide⟩),
   opAt 3480 .GT,
   opAt 3481 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3482 (.Dup ⟨0, by decide⟩),
   pushAt 3483 1 32,
   opAt 3484 .MLOAD,
   opAt 3485 .ADD,
   opAt 3486 (.Dup ⟨0, by decide⟩),
   pushAt 3487 2 2144,
   opAt 3488 .MLOAD,
   opAt 3489 (.Dup ⟨1, by decide⟩),
   opAt 3490 (.Dup ⟨1, by decide⟩),
   opAt 3491 .SUB,
   pushAt 3492 2 1824,
   opAt 3493 .MSTORE,
   opAt 3494 .LT,
   opAt 3495 (.Swap ⟨1, by decide⟩),
   opAt 3496 .GT,
   opAt 3497 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3498 (.Dup ⟨0, by decide⟩),
   pushAt 3499 0 0,
   opAt 3500 .MLOAD,
   opAt 3501 .ADD,
   opAt 3502 (.Dup ⟨0, by decide⟩),
   pushAt 3503 2 2112,
   opAt 3504 .MLOAD,
   opAt 3505 (.Dup ⟨1, by decide⟩),
   opAt 3506 (.Dup ⟨1, by decide⟩),
   opAt 3507 .SUB,
   pushAt 3508 2 1792,
   opAt 3509 .MSTORE,
   opAt 3510 .LT,
   opAt 3511 (.Swap ⟨1, by decide⟩),
   opAt 3512 .GT,
   opAt 3513 .OR]

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3379 = 4306 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4314 = true := by
  have h : Artifact.submissionArtifact.instructionPC 3383 = 4314 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [Artifact.instructionPC, h] using Artifact.isValidJumpDest_index 3383 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3520 = 4499 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3521 = 4502 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3522 = 4503 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3523 = 4504 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3524 = 4507 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3525 = 4508 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3526 = 4511 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3527 = 4512 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3528 = 4513 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3529 = 4516 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3530 = 4519 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3531 = 4520 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3532 = 4521 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3532 = 4521 := fixedPC3797

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3532 = 4521 := fixedPC3797

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3533 = 4522 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3534 = 4523 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3535 = 4524 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3536 = 4527 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3537 = 4530 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : Artifact.submissionArtifact.instructionPC 3380 = 4307 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3115 : Artifact.submissionArtifact.instructionPC 3381 = 4310 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3116 : Artifact.submissionArtifact.instructionPC 3382 = 4311 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3117 : Artifact.submissionArtifact.instructionPC 3383 = 4314 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3118 : Artifact.submissionArtifact.instructionPC 3384 = 4315 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3119 : Artifact.submissionArtifact.instructionPC 3385 = 4318 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : Artifact.submissionArtifact.instructionPC 3267 = 4148 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4156 = true := by
  have h : Artifact.submissionArtifact.instructionPC 3271 = 4156 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [Artifact.instructionPC, h] using Artifact.isValidJumpDest_index 3271 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3386 = 4319 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3387 = 4321 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3388 = 4322 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3389 = 4325 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPCs8 : Artifact.submissionArtifact.instructionPC 3390 = 4326 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3391 = 4327 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3392 = 4330 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3393 = 4331 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3394 = 4333 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3395 = 4334 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3396 = 4335 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3397 = 4336 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3397 = 4336 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3398 = 4337 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3399 = 4340 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3400 = 4341 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3401 = 4342 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3402 = 4343 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3403 = 4345 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3404 = 4346 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3405 = 4347 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3406 = 4348 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3407 = 4351 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3408 = 4352 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3409 = 4353 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3410 = 4354 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3411 = 4355 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3412 = 4358 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3413 = 4359 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3414 = 4360 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3414 = 4360 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3415 = 4361 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3416 = 4362 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3417 = 4363 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3418 = 4364 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3419 = 4366 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3420 = 4367 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3421 = 4368 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3422 = 4369 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3423 = 4372 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3424 = 4373 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3425 = 4374 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3426 = 4375 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3427 = 4376 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3428 = 4379 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3429 = 4380 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3430 = 4381 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3431 = 4382 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3431 = 4382 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3432 = 4383 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3433 = 4384 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3434 = 4385 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3435 = 4387 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3436 = 4388 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3437 = 4389 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3438 = 4390 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3439 = 4393 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3440 = 4394 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3441 = 4395 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3442 = 4396 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3443 = 4397 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3444 = 4400 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3445 = 4401 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3446 = 4402 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3447 = 4403 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3448 = 4404 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3448 = 4404 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3449 = 4405 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3450 = 4406 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3451 = 4408 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3452 = 4409 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3453 = 4410 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3454 = 4411 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3455 = 4414 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3456 = 4415 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3457 = 4416 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3458 = 4417 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3459 = 4418 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3460 = 4421 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3461 = 4422 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3462 = 4423 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3463 = 4424 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3464 = 4425 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3465 = 4426 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3465 = 4426 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4426 = true := by
  have h : Artifact.submissionArtifact.instructionPC 3465 = 4426 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [Artifact.instructionPC, h] using Artifact.isValidJumpDest_index 3465 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3466 = 4427 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3467 = 4428 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3468 = 4430 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3469 = 4431 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3470 = 4432 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3471 = 4433 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3472 = 4436 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3473 = 4437 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3474 = 4438 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3475 = 4439 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3476 = 4440 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3477 = 4443 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3478 = 4444 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3479 = 4445 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3480 = 4446 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3481 = 4447 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3482 = 4448 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3483 = 4449 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3483 = 4449 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3484 = 4451 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3485 = 4452 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3486 = 4453 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3487 = 4454 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3488 = 4457 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3489 = 4458 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3490 = 4459 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3491 = 4460 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3492 = 4461 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3493 = 4464 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3494 = 4465 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3495 = 4466 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3496 = 4467 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3497 = 4468 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3498 = 4469 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3499 = 4470 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3500 = 4471 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3500 = 4471 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3501 = 4472 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3502 = 4473 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3503 = 4474 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3504 = 4477 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3505 = 4478 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3506 = 4479 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3507 = 4480 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3508 = 4481 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3509 = 4484 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3510 = 4485 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3511 = 4486 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3512 = 4487 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3513 = 4488 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3514 = 4489 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3515 = 4490 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3516 = 4493 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3517 = 4494 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3517 = 4494 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3518 = 4495 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3519 = 4498 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3520 = 4499 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3521 = 4502 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3531 = 4520 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3531 = 4520 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3532 = 4521 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3533 = 4522 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3534 = 4523 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3535 = 4524 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3536 = 4527 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3537 = 4530 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3538 = 4531 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4190 : Artifact.submissionArtifact.instructionPC 3281 = 4171 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4193 : Artifact.submissionArtifact.instructionPC 3282 = 4172 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4194 : Artifact.submissionArtifact.instructionPC 3283 = 4175 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4547 : Artifact.submissionArtifact.instructionPC 3539 = 4532 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC4548 : Artifact.submissionArtifact.instructionPC 3540 = 4533 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3267 = 4148 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4156 = true := by
  have h : Artifact.submissionArtifact.instructionPC 3271 = 4156 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [Artifact.instructionPC, h] using Artifact.isValidJumpDest_index 3271 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3268 = 4151 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3269 = 4152 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3270 = 4155 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3271 = 4156 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3272 = 4157 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3273 = 4160 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3274 = 4161 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3275 = 4163 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3276 = 4164 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3277 = 4165 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3278 = 4166 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3279 = 4167 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3280 = 4170 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2603 = 3324 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3254 = 4131 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3255 = 4132 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3256 = 4133 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3257 = 4134 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3258 = 4135 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3259 = 4136 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3260 = 4137 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3261 = 4138 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3262 = 4141 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3263 = 4142 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3263 = 4142 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3264 = 4143 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3265 = 4146 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3266 = 4147 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2927 : Artifact.submissionArtifact.instructionPC 2603 = 3324 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3267 = 4148 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3268 = 4151 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3269 = 4152 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3270 = 4155 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3271 = 4156 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3272 = 4157 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3273 = 4160 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3274 = 4161 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3275 = 4163 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3276 = 4164 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3277 = 4165 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3278 = 4166 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3279 = 4167 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3280 = 4170 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 3523 = 4504 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 3524 = 4507 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 3525 = 4508 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 3526 = 4511 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 3527 = 4512 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 3528 = 4513 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 3529 = 4516 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 3530 = 4519 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast
