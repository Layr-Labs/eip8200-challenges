import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Located paths for the appended fused `ADDMOD`/conditional-subtract routine. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Fused routine entry, instructions 3398..3413, pc 5299..5320. -/
def blk3398 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3398 .JUMPDEST,
   pushAt 3399 4 8256,
   opAt 3400 (.Dup ⟨0, by decide⟩),
   opAt 3401 (.Swap ⟨1, by decide⟩),
   opAt 3402 .SUB,
   opAt 3403 (.Swap ⟨1, by decide⟩),
   opAt 3404 .SUB,
   opAt 3405 (.Swap ⟨0, by decide⟩),
   opAt 3406 .JUMPDEST,
   opAt 3407 .JUMPDEST,
   opAt 3408 .JUMPDEST,
   opAt 3409 .JUMPDEST,
   pushAt 3410 0 0,
   pushAt 3411 0 0,
   pushAt 3412 2 9440,
   opAt 3413 .MLOAD]

/-- Fused limb loop, instructions 3414..3468, pc 5321..5384. -/
def blk3414 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3414 .JUMPDEST,
   opAt 3415 (.Dup ⟨3, by decide⟩),
   opAt 3416 (.Dup ⟨1, by decide⟩),
   opAt 3417 .ADD,
   opAt 3418 .MLOAD,
   opAt 3419 (.Dup ⟨5, by decide⟩),
   opAt 3420 (.Dup ⟨2, by decide⟩),
   opAt 3421 .ADD,
   opAt 3422 .MLOAD,
   opAt 3423 (.Dup ⟨1, by decide⟩),
   opAt 3424 .ADD,
   opAt 3425 (.Dup ⟨0, by decide⟩),
   opAt 3426 (.Swap ⟨1, by decide⟩),
   opAt 3427 .GT,
   opAt 3428 (.Dup ⟨3, by decide⟩),
   opAt 3429 (.Dup ⟨2, by decide⟩),
   opAt 3430 .ADD,
   opAt 3431 (.Dup ⟨0, by decide⟩),
   opAt 3432 (.Swap ⟨2, by decide⟩),
   opAt 3433 .GT,
   opAt 3434 .OR,
   opAt 3435 (.Swap ⟨2, by decide⟩),
   opAt 3436 .POP,
   pushAt 3437 2 8256,
   opAt 3438 (.Dup ⟨2, by decide⟩),
   opAt 3439 .SUB,
   opAt 3440 .MLOAD,
   opAt 3441 (.Dup ⟨1, by decide⟩),
   opAt 3442 .SUB,
   opAt 3443 (.Dup ⟨0, by decide⟩),
   opAt 3444 (.Dup ⟨2, by decide⟩),
   opAt 3445 .LT,
   opAt 3446 (.Dup ⟨5, by decide⟩),
   opAt 3447 (.Dup ⟨2, by decide⟩),
   opAt 3448 .SUB,
   opAt 3449 (.Dup ⟨0, by decide⟩),
   opAt 3450 (.Swap ⟨2, by decide⟩),
   opAt 3451 .LT,
   opAt 3452 .OR,
   opAt 3453 (.Swap ⟨4, by decide⟩),
   opAt 3454 .POP,
   pushAt 3455 2 1088,
   opAt 3456 (.Dup ⟨3, by decide⟩),
   opAt 3457 .SUB,
   opAt 3458 .MSTORE,
   opAt 3459 (.Dup ⟨1, by decide⟩),
   opAt 3460 .MSTORE,
   pushAt 3461 1 32,
   opAt 3462 (.Swap ⟨0, by decide⟩),
   opAt 3463 .SUB,
   pushAt 3464 2 8224,
   opAt 3465 (.Dup ⟨1, by decide⟩),
   opAt 3466 .GT,
   pushAt 3467 2 5321,
   opAt 3468 .JUMPI]

/-- Fused selection and return, live instructions 3469..3487, pc 5385..5411; trailing padding is not executed. -/
def blk3469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3469 .POP,
   opAt 3470 (.Dup ⟨0, by decide⟩),
   pushAt 3471 2 8224,
   opAt 3472 .MSTORE,
   opAt 3473 (.Swap ⟨0, by decide⟩),
   opAt 3474 .ISZERO,
   opAt 3475 .OR,
   pushAt 3476 2 1088,
   opAt 3477 .MUL,
   pushAt 3478 2 8256,
   opAt 3479 .SUB,
   opAt 3480 (.Swap ⟨1, by decide⟩),
   opAt 3481 .POP,
   opAt 3482 .POP,
   pushAt 3483 2 9344,
   opAt 3484 .MLOAD,
   opAt 3485 (.Swap ⟨1, by decide⟩),
   opAt 3486 .MCOPY,
   opAt 3487 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
