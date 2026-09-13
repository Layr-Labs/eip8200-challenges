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
  [opAt 3373 .JUMPDEST,
   pushAt 3374 2 2688,
   opAt 3375 .MLOAD,
   pushAt 3376 2 256,
   opAt 3377 .EQ,
   pushAt 3378 2 4521,
   opAt 3379 .JUMPI,
   pushAt 3380 2 2688,
   opAt 3381 .MLOAD,
   pushAt 3382 1 128,
   opAt 3383 .EQ,
   pushAt 3384 2 4337,
   opAt 3385 .JUMPI,
   pushAt 3386 2 2784,
   opAt 3387 .MLOAD,
   pushAt 3388 2 2752,
   opAt 3389 .MLOAD,
   opAt 3390 (.Dup ⟨0, by decide⟩),
   pushAt 3391 2 1792,
   opAt 3392 .ADD,
   opAt 3393 (.Swap ⟨0, by decide⟩),
   pushAt 3394 0 0,
   opAt 3395 (.Swap ⟨2, by decide⟩),
   pushAt 3396 2 1574,
   opAt 3397 .JUMP]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3373 .JUMPDEST,
   pushAt 3374 2 2688,
   opAt 3375 .MLOAD,
   pushAt 3376 2 256,
   opAt 3377 .EQ,
   pushAt 3378 2 4521,
   opAt 3379 .JUMPI,
   opAt 3398 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3373 .JUMPDEST,
   pushAt 3374 2 2688,
   opAt 3375 .MLOAD,
   pushAt 3376 2 256,
   opAt 3377 .EQ,
   pushAt 3378 2 4521,
   opAt 3379 .JUMPI,
   pushAt 3380 2 2688,
   opAt 3381 .MLOAD,
   pushAt 3382 1 128,
   opAt 3383 .EQ,
   pushAt 3384 2 4337,
   opAt 3385 .JUMPI,
   opAt 3272 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3399 2 2336,
   opAt 3400 .MLOAD,
   pushAt 3401 1 224,
   opAt 3402 .MLOAD,
   opAt 3403 (.Dup ⟨1, by decide⟩),
   opAt 3404 (.Dup ⟨1, by decide⟩),
   opAt 3405 .GT,
   opAt 3406 (.Swap ⟨1, by decide⟩),
   opAt 3407 .SUB,
   pushAt 3408 2 2016,
   opAt 3409 .MSTORE]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3410 2 2304,
   opAt 3411 .MLOAD,
   pushAt 3412 1 192,
   opAt 3413 .MLOAD,
   opAt 3414 (.Dup ⟨1, by decide⟩),
   opAt 3415 (.Dup ⟨1, by decide⟩),
   opAt 3416 .GT,
   opAt 3417 (.Swap ⟨1, by decide⟩),
   opAt 3418 .SUB,
   opAt 3419 (.Dup ⟨2, by decide⟩),
   opAt 3420 (.Dup ⟨1, by decide⟩),
   opAt 3421 .SUB,
   opAt 3422 (.Swap ⟨2, by decide⟩),
   opAt 3423 .GT,
   opAt 3424 .OR,
   opAt 3425 (.Swap ⟨0, by decide⟩),
   pushAt 3426 2 1984,
   opAt 3427 .MSTORE]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3428 2 2272,
   opAt 3429 .MLOAD,
   pushAt 3430 1 160,
   opAt 3431 .MLOAD,
   opAt 3432 (.Dup ⟨1, by decide⟩),
   opAt 3433 (.Dup ⟨1, by decide⟩),
   opAt 3434 .GT,
   opAt 3435 (.Swap ⟨1, by decide⟩),
   opAt 3436 .SUB,
   opAt 3437 (.Dup ⟨2, by decide⟩),
   opAt 3438 (.Dup ⟨1, by decide⟩),
   opAt 3439 .SUB,
   opAt 3440 (.Swap ⟨2, by decide⟩),
   opAt 3441 .GT,
   opAt 3442 .OR,
   opAt 3443 (.Swap ⟨0, by decide⟩),
   pushAt 3444 2 1952,
   opAt 3445 .MSTORE]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3446 2 2240,
   opAt 3447 .MLOAD,
   pushAt 3448 1 128,
   opAt 3449 .MLOAD,
   opAt 3450 (.Dup ⟨1, by decide⟩),
   opAt 3451 (.Dup ⟨1, by decide⟩),
   opAt 3452 .GT,
   opAt 3453 (.Swap ⟨1, by decide⟩),
   opAt 3454 .SUB,
   opAt 3455 (.Dup ⟨2, by decide⟩),
   opAt 3456 (.Dup ⟨1, by decide⟩),
   opAt 3457 .SUB,
   opAt 3458 (.Swap ⟨2, by decide⟩),
   opAt 3459 .GT,
   opAt 3460 .OR,
   opAt 3461 (.Swap ⟨0, by decide⟩),
   pushAt 3462 2 1920,
   opAt 3463 .MSTORE]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 3464 2 2208,
   opAt 3465 .MLOAD,
   pushAt 3466 1 96,
   opAt 3467 .MLOAD,
   opAt 3468 (.Dup ⟨1, by decide⟩),
   opAt 3469 (.Dup ⟨1, by decide⟩),
   opAt 3470 .GT,
   opAt 3471 (.Swap ⟨1, by decide⟩),
   opAt 3472 .SUB,
   opAt 3473 (.Dup ⟨2, by decide⟩),
   opAt 3474 (.Dup ⟨1, by decide⟩),
   opAt 3475 .SUB,
   opAt 3476 (.Swap ⟨2, by decide⟩),
   opAt 3477 .GT,
   opAt 3478 .OR,
   opAt 3479 (.Swap ⟨0, by decide⟩),
   pushAt 3480 2 1888,
   opAt 3481 .MSTORE]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3482 .JUMPDEST,
   pushAt 3483 2 2176,
   opAt 3484 .MLOAD,
   pushAt 3485 1 64,
   opAt 3486 .MLOAD,
   opAt 3487 (.Dup ⟨1, by decide⟩),
   opAt 3488 (.Dup ⟨1, by decide⟩),
   opAt 3489 .GT,
   opAt 3490 (.Swap ⟨1, by decide⟩),
   opAt 3491 .SUB,
   opAt 3492 (.Dup ⟨2, by decide⟩),
   opAt 3493 (.Dup ⟨1, by decide⟩),
   opAt 3494 .SUB,
   opAt 3495 (.Swap ⟨2, by decide⟩),
   opAt 3496 .GT,
   opAt 3497 .OR,
   opAt 3498 (.Swap ⟨0, by decide⟩),
   pushAt 3499 2 1856,
   opAt 3500 .MSTORE]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3501 2 2144,
   opAt 3502 .MLOAD,
   pushAt 3503 1 32,
   opAt 3504 .MLOAD,
   opAt 3505 (.Dup ⟨1, by decide⟩),
   opAt 3506 (.Dup ⟨1, by decide⟩),
   opAt 3507 .GT,
   opAt 3508 (.Swap ⟨1, by decide⟩),
   opAt 3509 .SUB,
   opAt 3510 (.Dup ⟨2, by decide⟩),
   opAt 3511 (.Dup ⟨1, by decide⟩),
   opAt 3512 .SUB,
   opAt 3513 (.Swap ⟨2, by decide⟩),
   opAt 3514 .GT,
   opAt 3515 .OR,
   opAt 3516 (.Swap ⟨0, by decide⟩),
   pushAt 3517 2 1824,
   opAt 3518 .MSTORE]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3519 2 2112,
   opAt 3520 .MLOAD,
   pushAt 3521 0 0,
   opAt 3522 .MLOAD,
   opAt 3523 (.Dup ⟨1, by decide⟩),
   opAt 3524 (.Dup ⟨1, by decide⟩),
   opAt 3525 .GT,
   opAt 3526 (.Swap ⟨1, by decide⟩),
   opAt 3527 .SUB,
   opAt 3528 (.Dup ⟨2, by decide⟩),
   opAt 3529 (.Dup ⟨1, by decide⟩),
   opAt 3530 .SUB,
   opAt 3531 (.Swap ⟨2, by decide⟩),
   opAt 3532 .GT,
   opAt 3533 .OR,
   opAt 3534 (.Swap ⟨0, by decide⟩),
   pushAt 3535 2 1792,
   opAt 3536 .MSTORE]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3537 .ISZERO,
   pushAt 3538 2 2080,
   opAt 3539 .MLOAD,
   opAt 3540 .OR,
   pushAt 3541 2 319,
   opAt 3542 .NOT,
   pushAt 3543 2 4724,
   opAt 3544 .JUMP,
   opAt 3552 .JUMPDEST,
   opAt 3553 .MUL,
   pushAt 3554 2 2112,
   opAt 3555 .ADD,
   pushAt 3556 2 2688,
   opAt 3557 .MLOAD,
   opAt 3558 (.Swap ⟨1, by decide⟩),
   opAt 3559 .MCOPY,
   opAt 3560 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3273 2 2208,
   opAt 3274 .MLOAD,
   pushAt 3275 1 96,
   opAt 3276 .MLOAD,
   opAt 3277 (.Dup ⟨1, by decide⟩),
   opAt 3278 (.Dup ⟨1, by decide⟩),
   opAt 3279 .GT,
   opAt 3280 (.Swap ⟨1, by decide⟩),
   opAt 3281 .SUB,
   pushAt 3282 2 1888,
   opAt 3283 .MSTORE,
   pushAt 3284 2 4630,
   opAt 3285 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3482 .JUMPDEST,
   pushAt 3483 2 2176,
   opAt 3484 .MLOAD,
   pushAt 3485 1 64,
   opAt 3486 .MLOAD,
   opAt 3487 (.Dup ⟨1, by decide⟩),
   opAt 3488 (.Dup ⟨1, by decide⟩),
   opAt 3489 .GT,
   opAt 3490 (.Swap ⟨1, by decide⟩),
   opAt 3491 .SUB,
   opAt 3492 (.Dup ⟨2, by decide⟩),
   opAt 3493 (.Dup ⟨1, by decide⟩),
   opAt 3494 .SUB,
   opAt 3495 (.Swap ⟨2, by decide⟩),
   opAt 3496 .GT,
   opAt 3497 .OR,
   opAt 3498 (.Swap ⟨0, by decide⟩),
   pushAt 3499 2 1856,
   opAt 3500 .MSTORE]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3501 2 2144,
   opAt 3502 .MLOAD,
   pushAt 3503 1 32,
   opAt 3504 .MLOAD,
   opAt 3505 (.Dup ⟨1, by decide⟩),
   opAt 3506 (.Dup ⟨1, by decide⟩),
   opAt 3507 .GT,
   opAt 3508 (.Swap ⟨1, by decide⟩),
   opAt 3509 .SUB,
   opAt 3510 (.Dup ⟨2, by decide⟩),
   opAt 3511 (.Dup ⟨1, by decide⟩),
   opAt 3512 .SUB,
   opAt 3513 (.Swap ⟨2, by decide⟩),
   opAt 3514 .GT,
   opAt 3515 .OR,
   opAt 3516 (.Swap ⟨0, by decide⟩),
   pushAt 3517 2 1824,
   opAt 3518 .MSTORE]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3519 2 2112,
   opAt 3520 .MLOAD,
   pushAt 3521 0 0,
   opAt 3522 .MLOAD,
   opAt 3523 (.Dup ⟨1, by decide⟩),
   opAt 3524 (.Dup ⟨1, by decide⟩),
   opAt 3525 .GT,
   opAt 3526 (.Swap ⟨1, by decide⟩),
   opAt 3527 .SUB,
   opAt 3528 (.Dup ⟨2, by decide⟩),
   opAt 3529 (.Dup ⟨1, by decide⟩),
   opAt 3530 .SUB,
   opAt 3531 (.Swap ⟨2, by decide⟩),
   opAt 3532 .GT,
   opAt 3533 .OR,
   opAt 3534 (.Swap ⟨0, by decide⟩),
   pushAt 3535 2 1792,
   opAt 3536 .MSTORE]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3537 .ISZERO,
   pushAt 3538 2 2080,
   opAt 3539 .MLOAD,
   opAt 3540 .OR,
   pushAt 3541 2 319,
   opAt 3542 .NOT,
   pushAt 3543 2 4724,
   opAt 3544 .JUMP,
   opAt 3552 .JUMPDEST,
   opAt 3553 .MUL,
   pushAt 3554 2 2112,
   opAt 3555 .ADD,
   pushAt 3556 2 2688,
   opAt 3557 .MLOAD,
   opAt 3558 (.Swap ⟨1, by decide⟩),
   opAt 3559 .MCOPY,
   opAt 3560 .JUMP]

@[simp] theorem fixedPC1618 : Artifact.submissionArtifact.instructionPC 1105 = 1570 := by rfl

@[simp] theorem fixedPC1619 : Artifact.submissionArtifact.instructionPC 1106 = 1573 := by
  calc
    Artifact.submissionArtifact.instructionPC 1106 =
        Artifact.submissionArtifact.instructionPC 1105 + (YulEvmCompiler.Instr.push 2 4316).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1105 _ (by rfl)
    _ = 1573 := by rw [fixedPC1618]; rfl

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3373 = 4477 := by rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4477 = true := by
  simpa only [Artifact.instructionPC, fixedPC3777] using Artifact.isValidJumpDest_index 3373 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3374 = 4478 := by
  calc
    Artifact.submissionArtifact.instructionPC 3374 =
        Artifact.submissionArtifact.instructionPC 3373 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3373 _ (by rfl)
    _ = 4478 := by rw [fixedPC3777]; rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3375 = 4481 := by
  calc
    Artifact.submissionArtifact.instructionPC 3375 =
        Artifact.submissionArtifact.instructionPC 3374 + (YulEvmCompiler.Instr.push 2 2688).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3374 _ (by rfl)
    _ = 4481 := by rw [fixedPC3778]; rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3376 = 4482 := by
  calc
    Artifact.submissionArtifact.instructionPC 3376 =
        Artifact.submissionArtifact.instructionPC 3375 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3375 _ (by rfl)
    _ = 4482 := by rw [fixedPC3779]; rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3377 = 4485 := by
  calc
    Artifact.submissionArtifact.instructionPC 3377 =
        Artifact.submissionArtifact.instructionPC 3376 + (YulEvmCompiler.Instr.push 2 256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3376 _ (by rfl)
    _ = 4485 := by rw [fixedPC3780]; rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3378 = 4486 := by
  calc
    Artifact.submissionArtifact.instructionPC 3378 =
        Artifact.submissionArtifact.instructionPC 3377 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3377 _ (by rfl)
    _ = 4486 := by rw [fixedPC3781]; rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3379 = 4489 := by
  calc
    Artifact.submissionArtifact.instructionPC 3379 =
        Artifact.submissionArtifact.instructionPC 3378 + (YulEvmCompiler.Instr.push 2 4521).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3378 _ (by rfl)
    _ = 4489 := by rw [fixedPC3782]; rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3380 = 4490 := by
  calc
    Artifact.submissionArtifact.instructionPC 3380 =
        Artifact.submissionArtifact.instructionPC 3379 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3379 _ (by rfl)
    _ = 4490 := by rw [fixedPC3783]; rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3381 = 4493 := by
  calc
    Artifact.submissionArtifact.instructionPC 3381 =
        Artifact.submissionArtifact.instructionPC 3380 + (YulEvmCompiler.Instr.push 2 2688).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3380 _ (by rfl)
    _ = 4493 := by rw [fixedPC3784]; rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3382 = 4494 := by
  calc
    Artifact.submissionArtifact.instructionPC 3382 =
        Artifact.submissionArtifact.instructionPC 3381 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3381 _ (by rfl)
    _ = 4494 := by rw [fixedPC3785]; rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3383 = 4496 := by
  calc
    Artifact.submissionArtifact.instructionPC 3383 =
        Artifact.submissionArtifact.instructionPC 3382 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3382 _ (by rfl)
    _ = 4496 := by rw [fixedPC3786]; rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3384 = 4497 := by
  calc
    Artifact.submissionArtifact.instructionPC 3384 =
        Artifact.submissionArtifact.instructionPC 3383 + (YulEvmCompiler.Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3383 _ (by rfl)
    _ = 4497 := by rw [fixedPC3787]; rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3385 = 4500 := by
  calc
    Artifact.submissionArtifact.instructionPC 3385 =
        Artifact.submissionArtifact.instructionPC 3384 + (YulEvmCompiler.Instr.push 2 4337).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3384 _ (by rfl)
    _ = 4500 := by rw [fixedPC3788]; rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3386 = 4501 := by
  calc
    Artifact.submissionArtifact.instructionPC 3386 =
        Artifact.submissionArtifact.instructionPC 3385 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3385 _ (by rfl)
    _ = 4501 := by rw [fixedPC3789]; rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3387 = 4504 := by
  calc
    Artifact.submissionArtifact.instructionPC 3387 =
        Artifact.submissionArtifact.instructionPC 3386 + (YulEvmCompiler.Instr.push 2 2784).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3386 _ (by rfl)
    _ = 4504 := by rw [fixedPC3790]; rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3388 = 4505 := by
  calc
    Artifact.submissionArtifact.instructionPC 3388 =
        Artifact.submissionArtifact.instructionPC 3387 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3387 _ (by rfl)
    _ = 4505 := by rw [fixedPC3791]; rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3389 = 4508 := by
  calc
    Artifact.submissionArtifact.instructionPC 3389 =
        Artifact.submissionArtifact.instructionPC 3388 + (YulEvmCompiler.Instr.push 2 2752).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3388 _ (by rfl)
    _ = 4508 := by rw [fixedPC3792]; rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3390 = 4509 := by
  calc
    Artifact.submissionArtifact.instructionPC 3390 =
        Artifact.submissionArtifact.instructionPC 3389 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3389 _ (by rfl)
    _ = 4509 := by rw [fixedPC3793]; rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3391 = 4510 := by
  calc
    Artifact.submissionArtifact.instructionPC 3391 =
        Artifact.submissionArtifact.instructionPC 3390 + (YulEvmCompiler.Instr.op (.Dup ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3390 _ (by rfl)
    _ = 4510 := by rw [fixedPC3794]; rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3392 = 4513 := by
  calc
    Artifact.submissionArtifact.instructionPC 3392 =
        Artifact.submissionArtifact.instructionPC 3391 + (YulEvmCompiler.Instr.push 2 1792).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3391 _ (by rfl)
    _ = 4513 := by rw [fixedPC3795]; rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3393 = 4514 := by
  calc
    Artifact.submissionArtifact.instructionPC 3393 =
        Artifact.submissionArtifact.instructionPC 3392 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3392 _ (by rfl)
    _ = 4514 := by rw [fixedPC3796]; rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3393 = 4514 := fixedPC3797

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3393 = 4514 := fixedPC3797

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3394 = 4515 := by
  calc
    Artifact.submissionArtifact.instructionPC 3394 =
        Artifact.submissionArtifact.instructionPC 3393 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3393 _ (by rfl)
    _ = 4515 := by rw [fixedPC3799]; rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3395 = 4516 := by
  calc
    Artifact.submissionArtifact.instructionPC 3395 =
        Artifact.submissionArtifact.instructionPC 3394 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3394 _ (by rfl)
    _ = 4516 := by rw [fixedPC3800]; rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3396 = 4517 := by
  calc
    Artifact.submissionArtifact.instructionPC 3396 =
        Artifact.submissionArtifact.instructionPC 3395 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3395 _ (by rfl)
    _ = 4517 := by rw [fixedPC3801]; rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3397 = 4520 := by
  calc
    Artifact.submissionArtifact.instructionPC 3397 =
        Artifact.submissionArtifact.instructionPC 3396 + (YulEvmCompiler.Instr.push 2 1574).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3396 _ (by rfl)
    _ = 4520 := by rw [fixedPC3802]; rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3398 = 4521 := by
  calc
    Artifact.submissionArtifact.instructionPC 3398 =
        Artifact.submissionArtifact.instructionPC 3397 + (YulEvmCompiler.Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3397 _ (by rfl)
    _ = 4521 := by rw [fixedPC3803]; rfl

@[simp] theorem fixedJump5023 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4521 = true := by
  simpa only [Artifact.instructionPC, fixedPC3804] using Artifact.isValidJumpDest_index 3398 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3399 = 4522 := by
  calc
    Artifact.submissionArtifact.instructionPC 3399 =
        Artifact.submissionArtifact.instructionPC 3398 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3398 _ (by rfl)
    _ = 4522 := by rw [fixedPC3804]; rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3400 = 4525 := by
  calc
    Artifact.submissionArtifact.instructionPC 3400 =
        Artifact.submissionArtifact.instructionPC 3399 + (YulEvmCompiler.Instr.push 2 2336).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3399 _ (by rfl)
    _ = 4525 := by rw [fixedPC3805]; rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3401 = 4526 := by
  calc
    Artifact.submissionArtifact.instructionPC 3401 =
        Artifact.submissionArtifact.instructionPC 3400 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3400 _ (by rfl)
    _ = 4526 := by rw [fixedPC3806]; rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3402 = 4528 := by
  calc
    Artifact.submissionArtifact.instructionPC 3402 =
        Artifact.submissionArtifact.instructionPC 3401 + (YulEvmCompiler.Instr.push 1 224).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3401 _ (by rfl)
    _ = 4528 := by rw [fixedPC3807]; rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3403 = 4529 := by
  calc
    Artifact.submissionArtifact.instructionPC 3403 =
        Artifact.submissionArtifact.instructionPC 3402 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3402 _ (by rfl)
    _ = 4529 := by rw [fixedPC3808]; rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3404 = 4530 := by
  calc
    Artifact.submissionArtifact.instructionPC 3404 =
        Artifact.submissionArtifact.instructionPC 3403 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3403 _ (by rfl)
    _ = 4530 := by rw [fixedPC3809]; rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3405 = 4531 := by
  calc
    Artifact.submissionArtifact.instructionPC 3405 =
        Artifact.submissionArtifact.instructionPC 3404 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3404 _ (by rfl)
    _ = 4531 := by rw [fixedPC3810]; rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3406 = 4532 := by
  calc
    Artifact.submissionArtifact.instructionPC 3406 =
        Artifact.submissionArtifact.instructionPC 3405 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3405 _ (by rfl)
    _ = 4532 := by rw [fixedPC3811]; rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3407 = 4533 := by
  calc
    Artifact.submissionArtifact.instructionPC 3407 =
        Artifact.submissionArtifact.instructionPC 3406 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3406 _ (by rfl)
    _ = 4533 := by rw [fixedPC3812]; rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3408 = 4534 := by
  calc
    Artifact.submissionArtifact.instructionPC 3408 =
        Artifact.submissionArtifact.instructionPC 3407 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3407 _ (by rfl)
    _ = 4534 := by rw [fixedPC3813]; rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3409 = 4537 := by
  calc
    Artifact.submissionArtifact.instructionPC 3409 =
        Artifact.submissionArtifact.instructionPC 3408 + (YulEvmCompiler.Instr.push 2 2016).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3408 _ (by rfl)
    _ = 4537 := by rw [fixedPC3814]; rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3410 = 4538 := by
  calc
    Artifact.submissionArtifact.instructionPC 3410 =
        Artifact.submissionArtifact.instructionPC 3409 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3409 _ (by rfl)
    _ = 4538 := by rw [fixedPC3815]; rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3411 = 4541 := by
  calc
    Artifact.submissionArtifact.instructionPC 3411 =
        Artifact.submissionArtifact.instructionPC 3410 + (YulEvmCompiler.Instr.push 2 2304).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3410 _ (by rfl)
    _ = 4541 := by rw [fixedPC3816]; rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3412 = 4542 := by
  calc
    Artifact.submissionArtifact.instructionPC 3412 =
        Artifact.submissionArtifact.instructionPC 3411 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3411 _ (by rfl)
    _ = 4542 := by rw [fixedPC3817]; rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3413 = 4544 := by
  calc
    Artifact.submissionArtifact.instructionPC 3413 =
        Artifact.submissionArtifact.instructionPC 3412 + (YulEvmCompiler.Instr.push 1 192).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3412 _ (by rfl)
    _ = 4544 := by rw [fixedPC3818]; rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3414 = 4545 := by
  calc
    Artifact.submissionArtifact.instructionPC 3414 =
        Artifact.submissionArtifact.instructionPC 3413 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3413 _ (by rfl)
    _ = 4545 := by rw [fixedPC3819]; rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3415 = 4546 := by
  calc
    Artifact.submissionArtifact.instructionPC 3415 =
        Artifact.submissionArtifact.instructionPC 3414 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3414 _ (by rfl)
    _ = 4546 := by rw [fixedPC3820]; rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3416 = 4547 := by
  calc
    Artifact.submissionArtifact.instructionPC 3416 =
        Artifact.submissionArtifact.instructionPC 3415 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3415 _ (by rfl)
    _ = 4547 := by rw [fixedPC3821]; rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3417 = 4548 := by
  calc
    Artifact.submissionArtifact.instructionPC 3417 =
        Artifact.submissionArtifact.instructionPC 3416 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3416 _ (by rfl)
    _ = 4548 := by rw [fixedPC3822]; rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3418 = 4549 := by
  calc
    Artifact.submissionArtifact.instructionPC 3418 =
        Artifact.submissionArtifact.instructionPC 3417 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3417 _ (by rfl)
    _ = 4549 := by rw [fixedPC3823]; rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3419 = 4550 := by
  calc
    Artifact.submissionArtifact.instructionPC 3419 =
        Artifact.submissionArtifact.instructionPC 3418 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3418 _ (by rfl)
    _ = 4550 := by rw [fixedPC3824]; rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3420 = 4551 := by
  calc
    Artifact.submissionArtifact.instructionPC 3420 =
        Artifact.submissionArtifact.instructionPC 3419 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3419 _ (by rfl)
    _ = 4551 := by rw [fixedPC3825]; rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3421 = 4552 := by
  calc
    Artifact.submissionArtifact.instructionPC 3421 =
        Artifact.submissionArtifact.instructionPC 3420 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3420 _ (by rfl)
    _ = 4552 := by rw [fixedPC3826]; rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3422 = 4553 := by
  calc
    Artifact.submissionArtifact.instructionPC 3422 =
        Artifact.submissionArtifact.instructionPC 3421 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3421 _ (by rfl)
    _ = 4553 := by rw [fixedPC3827]; rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3423 = 4554 := by
  calc
    Artifact.submissionArtifact.instructionPC 3423 =
        Artifact.submissionArtifact.instructionPC 3422 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3422 _ (by rfl)
    _ = 4554 := by rw [fixedPC3828]; rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3424 = 4555 := by
  calc
    Artifact.submissionArtifact.instructionPC 3424 =
        Artifact.submissionArtifact.instructionPC 3423 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3423 _ (by rfl)
    _ = 4555 := by rw [fixedPC3829]; rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3425 = 4556 := by
  calc
    Artifact.submissionArtifact.instructionPC 3425 =
        Artifact.submissionArtifact.instructionPC 3424 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3424 _ (by rfl)
    _ = 4556 := by rw [fixedPC3830]; rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3426 = 4557 := by
  calc
    Artifact.submissionArtifact.instructionPC 3426 =
        Artifact.submissionArtifact.instructionPC 3425 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3425 _ (by rfl)
    _ = 4557 := by rw [fixedPC3831]; rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3427 = 4560 := by
  calc
    Artifact.submissionArtifact.instructionPC 3427 =
        Artifact.submissionArtifact.instructionPC 3426 + (YulEvmCompiler.Instr.push 2 1984).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3426 _ (by rfl)
    _ = 4560 := by rw [fixedPC3832]; rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3428 = 4561 := by
  calc
    Artifact.submissionArtifact.instructionPC 3428 =
        Artifact.submissionArtifact.instructionPC 3427 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3427 _ (by rfl)
    _ = 4561 := by rw [fixedPC3833]; rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3429 = 4564 := by
  calc
    Artifact.submissionArtifact.instructionPC 3429 =
        Artifact.submissionArtifact.instructionPC 3428 + (YulEvmCompiler.Instr.push 2 2272).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3428 _ (by rfl)
    _ = 4564 := by rw [fixedPC3834]; rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3430 = 4565 := by
  calc
    Artifact.submissionArtifact.instructionPC 3430 =
        Artifact.submissionArtifact.instructionPC 3429 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3429 _ (by rfl)
    _ = 4565 := by rw [fixedPC3835]; rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3431 = 4567 := by
  calc
    Artifact.submissionArtifact.instructionPC 3431 =
        Artifact.submissionArtifact.instructionPC 3430 + (YulEvmCompiler.Instr.push 1 160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3430 _ (by rfl)
    _ = 4567 := by rw [fixedPC3836]; rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3432 = 4568 := by
  calc
    Artifact.submissionArtifact.instructionPC 3432 =
        Artifact.submissionArtifact.instructionPC 3431 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3431 _ (by rfl)
    _ = 4568 := by rw [fixedPC3837]; rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3433 = 4569 := by
  calc
    Artifact.submissionArtifact.instructionPC 3433 =
        Artifact.submissionArtifact.instructionPC 3432 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3432 _ (by rfl)
    _ = 4569 := by rw [fixedPC3838]; rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3434 = 4570 := by
  calc
    Artifact.submissionArtifact.instructionPC 3434 =
        Artifact.submissionArtifact.instructionPC 3433 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3433 _ (by rfl)
    _ = 4570 := by rw [fixedPC3839]; rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3435 = 4571 := by
  calc
    Artifact.submissionArtifact.instructionPC 3435 =
        Artifact.submissionArtifact.instructionPC 3434 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3434 _ (by rfl)
    _ = 4571 := by rw [fixedPC3840]; rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3436 = 4572 := by
  calc
    Artifact.submissionArtifact.instructionPC 3436 =
        Artifact.submissionArtifact.instructionPC 3435 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3435 _ (by rfl)
    _ = 4572 := by rw [fixedPC3841]; rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3437 = 4573 := by
  calc
    Artifact.submissionArtifact.instructionPC 3437 =
        Artifact.submissionArtifact.instructionPC 3436 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3436 _ (by rfl)
    _ = 4573 := by rw [fixedPC3842]; rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3438 = 4574 := by
  calc
    Artifact.submissionArtifact.instructionPC 3438 =
        Artifact.submissionArtifact.instructionPC 3437 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3437 _ (by rfl)
    _ = 4574 := by rw [fixedPC3843]; rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3439 = 4575 := by
  calc
    Artifact.submissionArtifact.instructionPC 3439 =
        Artifact.submissionArtifact.instructionPC 3438 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3438 _ (by rfl)
    _ = 4575 := by rw [fixedPC3844]; rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3440 = 4576 := by
  calc
    Artifact.submissionArtifact.instructionPC 3440 =
        Artifact.submissionArtifact.instructionPC 3439 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3439 _ (by rfl)
    _ = 4576 := by rw [fixedPC3845]; rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3441 = 4577 := by
  calc
    Artifact.submissionArtifact.instructionPC 3441 =
        Artifact.submissionArtifact.instructionPC 3440 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3440 _ (by rfl)
    _ = 4577 := by rw [fixedPC3846]; rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3442 = 4578 := by
  calc
    Artifact.submissionArtifact.instructionPC 3442 =
        Artifact.submissionArtifact.instructionPC 3441 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3441 _ (by rfl)
    _ = 4578 := by rw [fixedPC3847]; rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3443 = 4579 := by
  calc
    Artifact.submissionArtifact.instructionPC 3443 =
        Artifact.submissionArtifact.instructionPC 3442 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3442 _ (by rfl)
    _ = 4579 := by rw [fixedPC3848]; rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3444 = 4580 := by
  calc
    Artifact.submissionArtifact.instructionPC 3444 =
        Artifact.submissionArtifact.instructionPC 3443 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3443 _ (by rfl)
    _ = 4580 := by rw [fixedPC3849]; rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3445 = 4583 := by
  calc
    Artifact.submissionArtifact.instructionPC 3445 =
        Artifact.submissionArtifact.instructionPC 3444 + (YulEvmCompiler.Instr.push 2 1952).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3444 _ (by rfl)
    _ = 4583 := by rw [fixedPC3850]; rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3446 = 4584 := by
  calc
    Artifact.submissionArtifact.instructionPC 3446 =
        Artifact.submissionArtifact.instructionPC 3445 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3445 _ (by rfl)
    _ = 4584 := by rw [fixedPC3851]; rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3447 = 4587 := by
  calc
    Artifact.submissionArtifact.instructionPC 3447 =
        Artifact.submissionArtifact.instructionPC 3446 + (YulEvmCompiler.Instr.push 2 2240).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3446 _ (by rfl)
    _ = 4587 := by rw [fixedPC3852]; rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3448 = 4588 := by
  calc
    Artifact.submissionArtifact.instructionPC 3448 =
        Artifact.submissionArtifact.instructionPC 3447 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3447 _ (by rfl)
    _ = 4588 := by rw [fixedPC3853]; rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3449 = 4590 := by
  calc
    Artifact.submissionArtifact.instructionPC 3449 =
        Artifact.submissionArtifact.instructionPC 3448 + (YulEvmCompiler.Instr.push 1 128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3448 _ (by rfl)
    _ = 4590 := by rw [fixedPC3854]; rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3450 = 4591 := by
  calc
    Artifact.submissionArtifact.instructionPC 3450 =
        Artifact.submissionArtifact.instructionPC 3449 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3449 _ (by rfl)
    _ = 4591 := by rw [fixedPC3855]; rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3451 = 4592 := by
  calc
    Artifact.submissionArtifact.instructionPC 3451 =
        Artifact.submissionArtifact.instructionPC 3450 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3450 _ (by rfl)
    _ = 4592 := by rw [fixedPC3856]; rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3452 = 4593 := by
  calc
    Artifact.submissionArtifact.instructionPC 3452 =
        Artifact.submissionArtifact.instructionPC 3451 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3451 _ (by rfl)
    _ = 4593 := by rw [fixedPC3857]; rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3453 = 4594 := by
  calc
    Artifact.submissionArtifact.instructionPC 3453 =
        Artifact.submissionArtifact.instructionPC 3452 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3452 _ (by rfl)
    _ = 4594 := by rw [fixedPC3858]; rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3454 = 4595 := by
  calc
    Artifact.submissionArtifact.instructionPC 3454 =
        Artifact.submissionArtifact.instructionPC 3453 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3453 _ (by rfl)
    _ = 4595 := by rw [fixedPC3859]; rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3455 = 4596 := by
  calc
    Artifact.submissionArtifact.instructionPC 3455 =
        Artifact.submissionArtifact.instructionPC 3454 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3454 _ (by rfl)
    _ = 4596 := by rw [fixedPC3860]; rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3456 = 4597 := by
  calc
    Artifact.submissionArtifact.instructionPC 3456 =
        Artifact.submissionArtifact.instructionPC 3455 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3455 _ (by rfl)
    _ = 4597 := by rw [fixedPC3861]; rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3457 = 4598 := by
  calc
    Artifact.submissionArtifact.instructionPC 3457 =
        Artifact.submissionArtifact.instructionPC 3456 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3456 _ (by rfl)
    _ = 4598 := by rw [fixedPC3862]; rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3458 = 4599 := by
  calc
    Artifact.submissionArtifact.instructionPC 3458 =
        Artifact.submissionArtifact.instructionPC 3457 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3457 _ (by rfl)
    _ = 4599 := by rw [fixedPC3863]; rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3459 = 4600 := by
  calc
    Artifact.submissionArtifact.instructionPC 3459 =
        Artifact.submissionArtifact.instructionPC 3458 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3458 _ (by rfl)
    _ = 4600 := by rw [fixedPC3864]; rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3460 = 4601 := by
  calc
    Artifact.submissionArtifact.instructionPC 3460 =
        Artifact.submissionArtifact.instructionPC 3459 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3459 _ (by rfl)
    _ = 4601 := by rw [fixedPC3865]; rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3461 = 4602 := by
  calc
    Artifact.submissionArtifact.instructionPC 3461 =
        Artifact.submissionArtifact.instructionPC 3460 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3460 _ (by rfl)
    _ = 4602 := by rw [fixedPC3866]; rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3462 = 4603 := by
  calc
    Artifact.submissionArtifact.instructionPC 3462 =
        Artifact.submissionArtifact.instructionPC 3461 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3461 _ (by rfl)
    _ = 4603 := by rw [fixedPC3867]; rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3463 = 4606 := by
  calc
    Artifact.submissionArtifact.instructionPC 3463 =
        Artifact.submissionArtifact.instructionPC 3462 + (YulEvmCompiler.Instr.push 2 1920).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3462 _ (by rfl)
    _ = 4606 := by rw [fixedPC3868]; rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3464 = 4607 := by
  calc
    Artifact.submissionArtifact.instructionPC 3464 =
        Artifact.submissionArtifact.instructionPC 3463 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3463 _ (by rfl)
    _ = 4607 := by rw [fixedPC3869]; rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3465 = 4610 := by
  calc
    Artifact.submissionArtifact.instructionPC 3465 =
        Artifact.submissionArtifact.instructionPC 3464 + (YulEvmCompiler.Instr.push 2 2208).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3464 _ (by rfl)
    _ = 4610 := by rw [fixedPC3871]; rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3466 = 4611 := by
  calc
    Artifact.submissionArtifact.instructionPC 3466 =
        Artifact.submissionArtifact.instructionPC 3465 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3465 _ (by rfl)
    _ = 4611 := by rw [fixedPC3872]; rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3467 = 4613 := by
  calc
    Artifact.submissionArtifact.instructionPC 3467 =
        Artifact.submissionArtifact.instructionPC 3466 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3466 _ (by rfl)
    _ = 4613 := by rw [fixedPC3873]; rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3468 = 4614 := by
  calc
    Artifact.submissionArtifact.instructionPC 3468 =
        Artifact.submissionArtifact.instructionPC 3467 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3467 _ (by rfl)
    _ = 4614 := by rw [fixedPC3874]; rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3469 = 4615 := by
  calc
    Artifact.submissionArtifact.instructionPC 3469 =
        Artifact.submissionArtifact.instructionPC 3468 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3468 _ (by rfl)
    _ = 4615 := by rw [fixedPC3875]; rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3470 = 4616 := by
  calc
    Artifact.submissionArtifact.instructionPC 3470 =
        Artifact.submissionArtifact.instructionPC 3469 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3469 _ (by rfl)
    _ = 4616 := by rw [fixedPC3876]; rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3471 = 4617 := by
  calc
    Artifact.submissionArtifact.instructionPC 3471 =
        Artifact.submissionArtifact.instructionPC 3470 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3470 _ (by rfl)
    _ = 4617 := by rw [fixedPC3877]; rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3472 = 4618 := by
  calc
    Artifact.submissionArtifact.instructionPC 3472 =
        Artifact.submissionArtifact.instructionPC 3471 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3471 _ (by rfl)
    _ = 4618 := by rw [fixedPC3878]; rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3473 = 4619 := by
  calc
    Artifact.submissionArtifact.instructionPC 3473 =
        Artifact.submissionArtifact.instructionPC 3472 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3472 _ (by rfl)
    _ = 4619 := by rw [fixedPC3879]; rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3474 = 4620 := by
  calc
    Artifact.submissionArtifact.instructionPC 3474 =
        Artifact.submissionArtifact.instructionPC 3473 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3473 _ (by rfl)
    _ = 4620 := by rw [fixedPC3880]; rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3475 = 4621 := by
  calc
    Artifact.submissionArtifact.instructionPC 3475 =
        Artifact.submissionArtifact.instructionPC 3474 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3474 _ (by rfl)
    _ = 4621 := by rw [fixedPC3881]; rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3476 = 4622 := by
  calc
    Artifact.submissionArtifact.instructionPC 3476 =
        Artifact.submissionArtifact.instructionPC 3475 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3475 _ (by rfl)
    _ = 4622 := by rw [fixedPC3882]; rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3477 = 4623 := by
  calc
    Artifact.submissionArtifact.instructionPC 3477 =
        Artifact.submissionArtifact.instructionPC 3476 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3476 _ (by rfl)
    _ = 4623 := by rw [fixedPC3883]; rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3478 = 4624 := by
  calc
    Artifact.submissionArtifact.instructionPC 3478 =
        Artifact.submissionArtifact.instructionPC 3477 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3477 _ (by rfl)
    _ = 4624 := by rw [fixedPC3884]; rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3479 = 4625 := by
  calc
    Artifact.submissionArtifact.instructionPC 3479 =
        Artifact.submissionArtifact.instructionPC 3478 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3478 _ (by rfl)
    _ = 4625 := by rw [fixedPC3885]; rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3480 = 4626 := by
  calc
    Artifact.submissionArtifact.instructionPC 3480 =
        Artifact.submissionArtifact.instructionPC 3479 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3479 _ (by rfl)
    _ = 4626 := by rw [fixedPC3886]; rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3481 = 4629 := by
  calc
    Artifact.submissionArtifact.instructionPC 3481 =
        Artifact.submissionArtifact.instructionPC 3480 + (YulEvmCompiler.Instr.push 2 1888).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3480 _ (by rfl)
    _ = 4629 := by rw [fixedPC3887]; rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3482 = 4630 := by
  calc
    Artifact.submissionArtifact.instructionPC 3482 =
        Artifact.submissionArtifact.instructionPC 3481 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3481 _ (by rfl)
    _ = 4630 := by rw [fixedPC3888]; rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4630 = true := by
  simpa only [Artifact.instructionPC, fixedPC3889] using Artifact.isValidJumpDest_index 3482 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3483 = 4631 := by
  calc
    Artifact.submissionArtifact.instructionPC 3483 =
        Artifact.submissionArtifact.instructionPC 3482 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3482 _ (by rfl)
    _ = 4631 := by rw [fixedPC3889]; rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3484 = 4634 := by
  calc
    Artifact.submissionArtifact.instructionPC 3484 =
        Artifact.submissionArtifact.instructionPC 3483 + (YulEvmCompiler.Instr.push 2 2176).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3483 _ (by rfl)
    _ = 4634 := by rw [fixedPC3890]; rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3485 = 4635 := by
  calc
    Artifact.submissionArtifact.instructionPC 3485 =
        Artifact.submissionArtifact.instructionPC 3484 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3484 _ (by rfl)
    _ = 4635 := by rw [fixedPC3891]; rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3486 = 4637 := by
  calc
    Artifact.submissionArtifact.instructionPC 3486 =
        Artifact.submissionArtifact.instructionPC 3485 + (YulEvmCompiler.Instr.push 1 64).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3485 _ (by rfl)
    _ = 4637 := by rw [fixedPC3892]; rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3487 = 4638 := by
  calc
    Artifact.submissionArtifact.instructionPC 3487 =
        Artifact.submissionArtifact.instructionPC 3486 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3486 _ (by rfl)
    _ = 4638 := by rw [fixedPC3893]; rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3488 = 4639 := by
  calc
    Artifact.submissionArtifact.instructionPC 3488 =
        Artifact.submissionArtifact.instructionPC 3487 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3487 _ (by rfl)
    _ = 4639 := by rw [fixedPC3894]; rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3489 = 4640 := by
  calc
    Artifact.submissionArtifact.instructionPC 3489 =
        Artifact.submissionArtifact.instructionPC 3488 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3488 _ (by rfl)
    _ = 4640 := by rw [fixedPC3895]; rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3490 = 4641 := by
  calc
    Artifact.submissionArtifact.instructionPC 3490 =
        Artifact.submissionArtifact.instructionPC 3489 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3489 _ (by rfl)
    _ = 4641 := by rw [fixedPC3896]; rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3491 = 4642 := by
  calc
    Artifact.submissionArtifact.instructionPC 3491 =
        Artifact.submissionArtifact.instructionPC 3490 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3490 _ (by rfl)
    _ = 4642 := by rw [fixedPC3897]; rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3492 = 4643 := by
  calc
    Artifact.submissionArtifact.instructionPC 3492 =
        Artifact.submissionArtifact.instructionPC 3491 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3491 _ (by rfl)
    _ = 4643 := by rw [fixedPC3898]; rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3493 = 4644 := by
  calc
    Artifact.submissionArtifact.instructionPC 3493 =
        Artifact.submissionArtifact.instructionPC 3492 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3492 _ (by rfl)
    _ = 4644 := by rw [fixedPC3899]; rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3494 = 4645 := by
  calc
    Artifact.submissionArtifact.instructionPC 3494 =
        Artifact.submissionArtifact.instructionPC 3493 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3493 _ (by rfl)
    _ = 4645 := by rw [fixedPC3900]; rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3495 = 4646 := by
  calc
    Artifact.submissionArtifact.instructionPC 3495 =
        Artifact.submissionArtifact.instructionPC 3494 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3494 _ (by rfl)
    _ = 4646 := by rw [fixedPC3901]; rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3496 = 4647 := by
  calc
    Artifact.submissionArtifact.instructionPC 3496 =
        Artifact.submissionArtifact.instructionPC 3495 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3495 _ (by rfl)
    _ = 4647 := by rw [fixedPC3902]; rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3497 = 4648 := by
  calc
    Artifact.submissionArtifact.instructionPC 3497 =
        Artifact.submissionArtifact.instructionPC 3496 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3496 _ (by rfl)
    _ = 4648 := by rw [fixedPC3903]; rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3498 = 4649 := by
  calc
    Artifact.submissionArtifact.instructionPC 3498 =
        Artifact.submissionArtifact.instructionPC 3497 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3497 _ (by rfl)
    _ = 4649 := by rw [fixedPC3904]; rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3499 = 4650 := by
  calc
    Artifact.submissionArtifact.instructionPC 3499 =
        Artifact.submissionArtifact.instructionPC 3498 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3498 _ (by rfl)
    _ = 4650 := by rw [fixedPC3905]; rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3500 = 4653 := by
  calc
    Artifact.submissionArtifact.instructionPC 3500 =
        Artifact.submissionArtifact.instructionPC 3499 + (YulEvmCompiler.Instr.push 2 1856).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3499 _ (by rfl)
    _ = 4653 := by rw [fixedPC3906]; rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3501 = 4654 := by
  calc
    Artifact.submissionArtifact.instructionPC 3501 =
        Artifact.submissionArtifact.instructionPC 3500 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3500 _ (by rfl)
    _ = 4654 := by rw [fixedPC3907]; rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3502 = 4657 := by
  calc
    Artifact.submissionArtifact.instructionPC 3502 =
        Artifact.submissionArtifact.instructionPC 3501 + (YulEvmCompiler.Instr.push 2 2144).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3501 _ (by rfl)
    _ = 4657 := by rw [fixedPC3908]; rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3503 = 4658 := by
  calc
    Artifact.submissionArtifact.instructionPC 3503 =
        Artifact.submissionArtifact.instructionPC 3502 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3502 _ (by rfl)
    _ = 4658 := by rw [fixedPC3909]; rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3504 = 4660 := by
  calc
    Artifact.submissionArtifact.instructionPC 3504 =
        Artifact.submissionArtifact.instructionPC 3503 + (YulEvmCompiler.Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3503 _ (by rfl)
    _ = 4660 := by rw [fixedPC3910]; rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3505 = 4661 := by
  calc
    Artifact.submissionArtifact.instructionPC 3505 =
        Artifact.submissionArtifact.instructionPC 3504 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3504 _ (by rfl)
    _ = 4661 := by rw [fixedPC3911]; rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3506 = 4662 := by
  calc
    Artifact.submissionArtifact.instructionPC 3506 =
        Artifact.submissionArtifact.instructionPC 3505 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3505 _ (by rfl)
    _ = 4662 := by rw [fixedPC3912]; rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3507 = 4663 := by
  calc
    Artifact.submissionArtifact.instructionPC 3507 =
        Artifact.submissionArtifact.instructionPC 3506 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3506 _ (by rfl)
    _ = 4663 := by rw [fixedPC3913]; rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3508 = 4664 := by
  calc
    Artifact.submissionArtifact.instructionPC 3508 =
        Artifact.submissionArtifact.instructionPC 3507 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3507 _ (by rfl)
    _ = 4664 := by rw [fixedPC3914]; rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3509 = 4665 := by
  calc
    Artifact.submissionArtifact.instructionPC 3509 =
        Artifact.submissionArtifact.instructionPC 3508 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3508 _ (by rfl)
    _ = 4665 := by rw [fixedPC3915]; rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3510 = 4666 := by
  calc
    Artifact.submissionArtifact.instructionPC 3510 =
        Artifact.submissionArtifact.instructionPC 3509 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3509 _ (by rfl)
    _ = 4666 := by rw [fixedPC3916]; rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3511 = 4667 := by
  calc
    Artifact.submissionArtifact.instructionPC 3511 =
        Artifact.submissionArtifact.instructionPC 3510 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3510 _ (by rfl)
    _ = 4667 := by rw [fixedPC3917]; rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3512 = 4668 := by
  calc
    Artifact.submissionArtifact.instructionPC 3512 =
        Artifact.submissionArtifact.instructionPC 3511 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3511 _ (by rfl)
    _ = 4668 := by rw [fixedPC3918]; rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3513 = 4669 := by
  calc
    Artifact.submissionArtifact.instructionPC 3513 =
        Artifact.submissionArtifact.instructionPC 3512 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3512 _ (by rfl)
    _ = 4669 := by rw [fixedPC3919]; rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3514 = 4670 := by
  calc
    Artifact.submissionArtifact.instructionPC 3514 =
        Artifact.submissionArtifact.instructionPC 3513 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3513 _ (by rfl)
    _ = 4670 := by rw [fixedPC3920]; rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3515 = 4671 := by
  calc
    Artifact.submissionArtifact.instructionPC 3515 =
        Artifact.submissionArtifact.instructionPC 3514 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3514 _ (by rfl)
    _ = 4671 := by rw [fixedPC3921]; rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3516 = 4672 := by
  calc
    Artifact.submissionArtifact.instructionPC 3516 =
        Artifact.submissionArtifact.instructionPC 3515 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3515 _ (by rfl)
    _ = 4672 := by rw [fixedPC3922]; rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3517 = 4673 := by
  calc
    Artifact.submissionArtifact.instructionPC 3517 =
        Artifact.submissionArtifact.instructionPC 3516 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3516 _ (by rfl)
    _ = 4673 := by rw [fixedPC3923]; rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3518 = 4676 := by
  calc
    Artifact.submissionArtifact.instructionPC 3518 =
        Artifact.submissionArtifact.instructionPC 3517 + (YulEvmCompiler.Instr.push 2 1824).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3517 _ (by rfl)
    _ = 4676 := by rw [fixedPC3924]; rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3519 = 4677 := by
  calc
    Artifact.submissionArtifact.instructionPC 3519 =
        Artifact.submissionArtifact.instructionPC 3518 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3518 _ (by rfl)
    _ = 4677 := by rw [fixedPC3925]; rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3520 = 4680 := by
  calc
    Artifact.submissionArtifact.instructionPC 3520 =
        Artifact.submissionArtifact.instructionPC 3519 + (YulEvmCompiler.Instr.push 2 2112).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3519 _ (by rfl)
    _ = 4680 := by rw [fixedPC3926]; rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3521 = 4681 := by
  calc
    Artifact.submissionArtifact.instructionPC 3521 =
        Artifact.submissionArtifact.instructionPC 3520 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3520 _ (by rfl)
    _ = 4681 := by rw [fixedPC3927]; rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3522 = 4682 := by
  calc
    Artifact.submissionArtifact.instructionPC 3522 =
        Artifact.submissionArtifact.instructionPC 3521 + (YulEvmCompiler.Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3521 _ (by rfl)
    _ = 4682 := by rw [fixedPC3928]; rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3523 = 4683 := by
  calc
    Artifact.submissionArtifact.instructionPC 3523 =
        Artifact.submissionArtifact.instructionPC 3522 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3522 _ (by rfl)
    _ = 4683 := by rw [fixedPC3929]; rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3524 = 4684 := by
  calc
    Artifact.submissionArtifact.instructionPC 3524 =
        Artifact.submissionArtifact.instructionPC 3523 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3523 _ (by rfl)
    _ = 4684 := by rw [fixedPC3930]; rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3525 = 4685 := by
  calc
    Artifact.submissionArtifact.instructionPC 3525 =
        Artifact.submissionArtifact.instructionPC 3524 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3524 _ (by rfl)
    _ = 4685 := by rw [fixedPC3931]; rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3526 = 4686 := by
  calc
    Artifact.submissionArtifact.instructionPC 3526 =
        Artifact.submissionArtifact.instructionPC 3525 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3525 _ (by rfl)
    _ = 4686 := by rw [fixedPC3932]; rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3527 = 4687 := by
  calc
    Artifact.submissionArtifact.instructionPC 3527 =
        Artifact.submissionArtifact.instructionPC 3526 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3526 _ (by rfl)
    _ = 4687 := by rw [fixedPC3933]; rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3528 = 4688 := by
  calc
    Artifact.submissionArtifact.instructionPC 3528 =
        Artifact.submissionArtifact.instructionPC 3527 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3527 _ (by rfl)
    _ = 4688 := by rw [fixedPC3934]; rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3529 = 4689 := by
  calc
    Artifact.submissionArtifact.instructionPC 3529 =
        Artifact.submissionArtifact.instructionPC 3528 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3528 _ (by rfl)
    _ = 4689 := by rw [fixedPC3935]; rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3530 = 4690 := by
  calc
    Artifact.submissionArtifact.instructionPC 3530 =
        Artifact.submissionArtifact.instructionPC 3529 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3529 _ (by rfl)
    _ = 4690 := by rw [fixedPC3936]; rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3531 = 4691 := by
  calc
    Artifact.submissionArtifact.instructionPC 3531 =
        Artifact.submissionArtifact.instructionPC 3530 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3530 _ (by rfl)
    _ = 4691 := by rw [fixedPC3937]; rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3532 = 4692 := by
  calc
    Artifact.submissionArtifact.instructionPC 3532 =
        Artifact.submissionArtifact.instructionPC 3531 + (YulEvmCompiler.Instr.op (.Swap ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3531 _ (by rfl)
    _ = 4692 := by rw [fixedPC3938]; rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3533 = 4693 := by
  calc
    Artifact.submissionArtifact.instructionPC 3533 =
        Artifact.submissionArtifact.instructionPC 3532 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3532 _ (by rfl)
    _ = 4693 := by rw [fixedPC3939]; rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3534 = 4694 := by
  calc
    Artifact.submissionArtifact.instructionPC 3534 =
        Artifact.submissionArtifact.instructionPC 3533 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3533 _ (by rfl)
    _ = 4694 := by rw [fixedPC3940]; rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3535 = 4695 := by
  calc
    Artifact.submissionArtifact.instructionPC 3535 =
        Artifact.submissionArtifact.instructionPC 3534 + (YulEvmCompiler.Instr.op (.Swap ⟨0, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3534 _ (by rfl)
    _ = 4695 := by rw [fixedPC3941]; rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3536 = 4698 := by
  calc
    Artifact.submissionArtifact.instructionPC 3536 =
        Artifact.submissionArtifact.instructionPC 3535 + (YulEvmCompiler.Instr.push 2 1792).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3535 _ (by rfl)
    _ = 4698 := by rw [fixedPC3942]; rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3537 = 4699 := by
  calc
    Artifact.submissionArtifact.instructionPC 3537 =
        Artifact.submissionArtifact.instructionPC 3536 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3536 _ (by rfl)
    _ = 4699 := by rw [fixedPC3943]; rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3538 = 4700 := by
  calc
    Artifact.submissionArtifact.instructionPC 3538 =
        Artifact.submissionArtifact.instructionPC 3537 + (YulEvmCompiler.Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3537 _ (by rfl)
    _ = 4700 := by rw [fixedPC3944]; rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3539 = 4703 := by
  calc
    Artifact.submissionArtifact.instructionPC 3539 =
        Artifact.submissionArtifact.instructionPC 3538 + (YulEvmCompiler.Instr.push 2 2080).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3538 _ (by rfl)
    _ = 4703 := by rw [fixedPC3945]; rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3540 = 4704 := by
  calc
    Artifact.submissionArtifact.instructionPC 3540 =
        Artifact.submissionArtifact.instructionPC 3539 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3539 _ (by rfl)
    _ = 4704 := by rw [fixedPC3946]; rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3541 = 4705 := by
  calc
    Artifact.submissionArtifact.instructionPC 3541 =
        Artifact.submissionArtifact.instructionPC 3540 + (YulEvmCompiler.Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3540 _ (by rfl)
    _ = 4705 := by rw [fixedPC3947]; rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3553 = 4725 := by
  decide

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3553 = 4725 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3554 = 4726 := by
  calc
    Artifact.submissionArtifact.instructionPC 3554 =
        Artifact.submissionArtifact.instructionPC 3553 + (YulEvmCompiler.Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3553 _ (by rfl)
    _ = 4726 := by rw [fixedPC3950]; rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3555 = 4729 := by
  calc
    Artifact.submissionArtifact.instructionPC 3555 =
        Artifact.submissionArtifact.instructionPC 3554 + (YulEvmCompiler.Instr.push 2 2112).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3554 _ (by rfl)
    _ = 4729 := by rw [fixedPC3951]; rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3556 = 4730 := by
  calc
    Artifact.submissionArtifact.instructionPC 3556 =
        Artifact.submissionArtifact.instructionPC 3555 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3555 _ (by rfl)
    _ = 4730 := by rw [fixedPC3952]; rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3557 = 4733 := by
  calc
    Artifact.submissionArtifact.instructionPC 3557 =
        Artifact.submissionArtifact.instructionPC 3556 + (YulEvmCompiler.Instr.push 2 2688).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3556 _ (by rfl)
    _ = 4733 := by rw [fixedPC3953]; rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3558 = 4734 := by
  calc
    Artifact.submissionArtifact.instructionPC 3558 =
        Artifact.submissionArtifact.instructionPC 3557 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3557 _ (by rfl)
    _ = 4734 := by rw [fixedPC3954]; rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3559 = 4735 := by
  calc
    Artifact.submissionArtifact.instructionPC 3559 =
        Artifact.submissionArtifact.instructionPC 3558 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3558 _ (by rfl)
    _ = 4735 := by rw [fixedPC3955]; rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3560 = 4736 := by
  calc
    Artifact.submissionArtifact.instructionPC 3560 =
        Artifact.submissionArtifact.instructionPC 3559 + (YulEvmCompiler.Instr.op .MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3559 _ (by rfl)
    _ = 4736 := by rw [fixedPC3956]; rfl

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

@[simp] theorem fixedPC3977 : Artifact.submissionArtifact.instructionPC 18 = 25 := by rfl

@[simp] theorem fixedPC3978 : Artifact.submissionArtifact.instructionPC 19 = 26 := by
  calc
    Artifact.submissionArtifact.instructionPC 19 =
        Artifact.submissionArtifact.instructionPC 18 + (YulEvmCompiler.Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 18 _ (by rfl)
    _ = 26 := by rw [fixedPC3977]; rfl

@[simp] theorem fixedPC3979 : Artifact.submissionArtifact.instructionPC 20 = 27 := by
  calc
    Artifact.submissionArtifact.instructionPC 20 =
        Artifact.submissionArtifact.instructionPC 19 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 19 _ (by rfl)
    _ = 27 := by rw [fixedPC3978]; rfl

@[simp] theorem fixedPC3980 : Artifact.submissionArtifact.instructionPC 21 = 29 := by
  calc
    Artifact.submissionArtifact.instructionPC 21 =
        Artifact.submissionArtifact.instructionPC 20 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 20 _ (by rfl)
    _ = 29 := by rw [fixedPC3979]; rfl

@[simp] theorem fixedPC3981 : Artifact.submissionArtifact.instructionPC 22 = 30 := by
  calc
    Artifact.submissionArtifact.instructionPC 22 =
        Artifact.submissionArtifact.instructionPC 21 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 21 _ (by rfl)
    _ = 30 := by rw [fixedPC3980]; rfl

@[simp] theorem fixedPC3982 : Artifact.submissionArtifact.instructionPC 23 = 31 := by
  calc
    Artifact.submissionArtifact.instructionPC 23 =
        Artifact.submissionArtifact.instructionPC 22 + (YulEvmCompiler.Instr.op (.Dup ⟨2, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 22 _ (by rfl)
    _ = 31 := by rw [fixedPC3981]; rfl

@[simp] theorem fixedPC3983 : Artifact.submissionArtifact.instructionPC 24 = 32 := by
  calc
    Artifact.submissionArtifact.instructionPC 24 =
        Artifact.submissionArtifact.instructionPC 23 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 23 _ (by rfl)
    _ = 32 := by rw [fixedPC3982]; rfl

@[simp] theorem fixedPC3984 : Artifact.submissionArtifact.instructionPC 25 = 33 := by
  calc
    Artifact.submissionArtifact.instructionPC 25 =
        Artifact.submissionArtifact.instructionPC 24 + (YulEvmCompiler.Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 24 _ (by rfl)
    _ = 33 := by rw [fixedPC3983]; rfl

@[simp] theorem fixedPC3985 : Artifact.submissionArtifact.instructionPC 26 = 36 := by
  calc
    Artifact.submissionArtifact.instructionPC 26 =
        Artifact.submissionArtifact.instructionPC 25 + (YulEvmCompiler.Instr.push 2 1186).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 25 _ (by rfl)
    _ = 36 := by rw [fixedPC3984]; rfl

@[simp] theorem fixedPC3986 : Artifact.submissionArtifact.instructionPC 27 = 37 := by
  calc
    Artifact.submissionArtifact.instructionPC 27 =
        Artifact.submissionArtifact.instructionPC 26 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 26 _ (by rfl)
    _ = 37 := by rw [fixedPC3985]; rfl

@[simp] theorem fixedPC3987 : Artifact.submissionArtifact.instructionPC 28 = 38 := by
  calc
    Artifact.submissionArtifact.instructionPC 28 =
        Artifact.submissionArtifact.instructionPC 27 + (YulEvmCompiler.Instr.op (.Dup ⟨3, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 27 _ (by rfl)
    _ = 38 := by rw [fixedPC3986]; rfl

@[simp] theorem fixedPC3988 : Artifact.submissionArtifact.instructionPC 29 = 40 := by
  calc
    Artifact.submissionArtifact.instructionPC 29 =
        Artifact.submissionArtifact.instructionPC 28 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 28 _ (by rfl)
    _ = 40 := by rw [fixedPC3987]; rfl

@[simp] theorem fixedPC3989 : Artifact.submissionArtifact.instructionPC 30 = 41 := by
  calc
    Artifact.submissionArtifact.instructionPC 30 =
        Artifact.submissionArtifact.instructionPC 29 + (YulEvmCompiler.Instr.op (.Dup ⟨6, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 29 _ (by rfl)
    _ = 41 := by rw [fixedPC3988]; rfl

@[simp] theorem fixedPC3990 : Artifact.submissionArtifact.instructionPC 31 = 42 := by
  calc
    Artifact.submissionArtifact.instructionPC 31 =
        Artifact.submissionArtifact.instructionPC 30 + (YulEvmCompiler.Instr.op (.Dup ⟨8, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 30 _ (by rfl)
    _ = 42 := by rw [fixedPC3989]; rfl

@[simp] theorem fixedPC3991 : Artifact.submissionArtifact.instructionPC 32 = 43 := by
  calc
    Artifact.submissionArtifact.instructionPC 32 =
        Artifact.submissionArtifact.instructionPC 31 + (YulEvmCompiler.Instr.op (.Dup ⟨10, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 31 _ (by rfl)
    _ = 43 := by rw [fixedPC3990]; rfl

@[simp] theorem fixedPC3992 : Artifact.submissionArtifact.instructionPC 32 = 43 := by rfl

@[simp] theorem fixedPC3993 : Artifact.submissionArtifact.instructionPC 70 = 127 := by rfl

@[simp] theorem fixedJump5272 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 127 = true := by
  simpa only [Artifact.instructionPC, fixedPC3993] using Artifact.isValidJumpDest_index 70 (by rfl)

@[simp] theorem fixedPC3994 : Artifact.submissionArtifact.instructionPC 71 = 128 := by
  calc
    Artifact.submissionArtifact.instructionPC 71 =
        Artifact.submissionArtifact.instructionPC 70 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 70 _ (by rfl)
    _ = 128 := by rw [fixedPC3993]; rfl

@[simp] theorem fixedPC3995 : Artifact.submissionArtifact.instructionPC 72 = 129 := by
  calc
    Artifact.submissionArtifact.instructionPC 72 =
        Artifact.submissionArtifact.instructionPC 71 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 71 _ (by rfl)
    _ = 129 := by rw [fixedPC3994]; rfl

@[simp] theorem fixedPC3996 : Artifact.submissionArtifact.instructionPC 73 = 130 := by
  calc
    Artifact.submissionArtifact.instructionPC 73 =
        Artifact.submissionArtifact.instructionPC 72 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 72 _ (by rfl)
    _ = 130 := by rw [fixedPC3995]; rfl

@[simp] theorem fixedPC3997 : Artifact.submissionArtifact.instructionPC 74 = 131 := by
  calc
    Artifact.submissionArtifact.instructionPC 74 =
        Artifact.submissionArtifact.instructionPC 73 + (YulEvmCompiler.Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 73 _ (by rfl)
    _ = 131 := by rw [fixedPC3996]; rfl

@[simp] theorem fixedPC3998 : Artifact.submissionArtifact.instructionPC 75 = 134 := by
  calc
    Artifact.submissionArtifact.instructionPC 75 =
        Artifact.submissionArtifact.instructionPC 74 + (YulEvmCompiler.Instr.push 2 717).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 74 _ (by rfl)
    _ = 134 := by rw [fixedPC3997]; rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3272 = 4337 := by
  decide

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4337 = true := by
  simpa only [Artifact.instructionPC, fixedPC3999] using Artifact.isValidJumpDest_index 3272 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3273 = 4338 := by
  calc
    Artifact.submissionArtifact.instructionPC 3273 =
        Artifact.submissionArtifact.instructionPC 3272 + (YulEvmCompiler.Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3272 _ (by rfl)
    _ = 4338 := by rw [fixedPC3999]; rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3274 = 4341 := by
  calc
    Artifact.submissionArtifact.instructionPC 3274 =
        Artifact.submissionArtifact.instructionPC 3273 + (YulEvmCompiler.Instr.push 2 2208).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3273 _ (by rfl)
    _ = 4341 := by rw [fixedPC4000]; rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3275 = 4342 := by
  calc
    Artifact.submissionArtifact.instructionPC 3275 =
        Artifact.submissionArtifact.instructionPC 3274 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3274 _ (by rfl)
    _ = 4342 := by rw [fixedPC4001]; rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3276 = 4344 := by
  calc
    Artifact.submissionArtifact.instructionPC 3276 =
        Artifact.submissionArtifact.instructionPC 3275 + (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3275 _ (by rfl)
    _ = 4344 := by rw [fixedPC4002]; rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3277 = 4345 := by
  calc
    Artifact.submissionArtifact.instructionPC 3277 =
        Artifact.submissionArtifact.instructionPC 3276 + (YulEvmCompiler.Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3276 _ (by rfl)
    _ = 4345 := by rw [fixedPC4003]; rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3278 = 4346 := by
  calc
    Artifact.submissionArtifact.instructionPC 3278 =
        Artifact.submissionArtifact.instructionPC 3277 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3277 _ (by rfl)
    _ = 4346 := by rw [fixedPC4004]; rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3279 = 4347 := by
  calc
    Artifact.submissionArtifact.instructionPC 3279 =
        Artifact.submissionArtifact.instructionPC 3278 + (YulEvmCompiler.Instr.op (.Dup ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3278 _ (by rfl)
    _ = 4347 := by rw [fixedPC4005]; rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3280 = 4348 := by
  calc
    Artifact.submissionArtifact.instructionPC 3280 =
        Artifact.submissionArtifact.instructionPC 3279 + (YulEvmCompiler.Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3279 _ (by rfl)
    _ = 4348 := by rw [fixedPC4006]; rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3281 = 4349 := by
  calc
    Artifact.submissionArtifact.instructionPC 3281 =
        Artifact.submissionArtifact.instructionPC 3280 + (YulEvmCompiler.Instr.op (.Swap ⟨1, by decide⟩)).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3280 _ (by rfl)
    _ = 4349 := by rw [fixedPC4007]; rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3282 = 4350 := by
  calc
    Artifact.submissionArtifact.instructionPC 3282 =
        Artifact.submissionArtifact.instructionPC 3281 + (YulEvmCompiler.Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3281 _ (by rfl)
    _ = 4350 := by rw [fixedPC4008]; rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3283 = 4353 := by
  calc
    Artifact.submissionArtifact.instructionPC 3283 =
        Artifact.submissionArtifact.instructionPC 3282 + (YulEvmCompiler.Instr.push 2 1888).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3282 _ (by rfl)
    _ = 4353 := by rw [fixedPC4009]; rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3284 = 4354 := by
  calc
    Artifact.submissionArtifact.instructionPC 3284 =
        Artifact.submissionArtifact.instructionPC 3283 + (YulEvmCompiler.Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3283 _ (by rfl)
    _ = 4354 := by rw [fixedPC4010]; rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3285 = 4357 := by
  calc
    Artifact.submissionArtifact.instructionPC 3285 =
        Artifact.submissionArtifact.instructionPC 3284 + (YulEvmCompiler.Instr.push 2 4630).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3284 _ (by rfl)
    _ = 4357 := by rw [fixedPC4011]; rfl


@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2475 = 3320 := by rfl
@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3259 = 4316 := by rfl
@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3260 = 4317 := by rfl
@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3261 = 4318 := by rfl
@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3262 = 4319 := by rfl
@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3263 = 4322 := by rfl
@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3264 = 4323 := by rfl
@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3265 = 4324 := by rfl
@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3266 = 4327 := by rfl
@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3267 = 4328 := by rfl
@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3268 = 4329 := by rfl
@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3268 = 4329 := by rfl
@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3269 = 4332 := by rfl
@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3270 = 4333 := by rfl
@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3271 = 4336 := by rfl
@[simp] theorem earlyExtraPC2927 : Artifact.submissionArtifact.instructionPC 2475 = 3320 := by rfl
@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3272 = 4337 := by rfl
@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3273 = 4338 := by rfl
@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3274 = 4341 := by rfl
@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3275 = 4342 := by rfl
@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3276 = 4344 := by rfl
@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3277 = 4345 := by rfl
@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3278 = 4346 := by rfl
@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3279 = 4347 := by rfl
@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3280 = 4348 := by rfl
@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3281 = 4349 := by rfl
@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3282 = 4350 := by rfl
@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3283 = 4353 := by rfl
@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3284 = 4354 := by rfl
@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3285 = 4357 := by rfl
@[simp] theorem earlyExtraPC3918 : Artifact.submissionArtifact.instructionPC 3542 = 4708 := by rfl
@[simp] theorem earlyExtraPC3919 : Artifact.submissionArtifact.instructionPC 3543 = 4709 := by rfl
@[simp] theorem earlyExtraPC3920 : Artifact.submissionArtifact.instructionPC 3544 = 4712 := by rfl
@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 3545 = 4713 := by rfl
@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 3546 = 4714 := by rfl
@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 3547 = 4717 := by rfl
@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 3548 = 4720 := by rfl
@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 3549 = 4721 := by rfl
@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 3550 = 4722 := by rfl
@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 3551 = 4723 := by rfl
@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 3552 = 4724 := by rfl
end Challenge.Modexp.Submission.Proofs.Fast
