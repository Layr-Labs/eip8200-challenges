import Challenge.Modexp.Submission.Proofs.Fast.ShiftPaths
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Loop-body blocks of the shift-reduce routine split before their exit tests, so
that each block reduction stays small enough for the kernel. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The negation loop body up to its exit test (`blk2896` instructions 0..14). -/
def blk2896a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3162 .JUMPDEST,
   opAt 3163 (.Dup ⟨0, by decide⟩),
   opAt 3164 .MLOAD,
   opAt 3165 .NOT,
   opAt 3166 (.Dup ⟨2, by decide⟩),
   opAt 3167 .ADD,
   opAt 3168 (.Dup ⟨2, by decide⟩),
   opAt 3169 (.Dup ⟨1, by decide⟩),
   opAt 3170 .LT,
   opAt 3171 (.Swap ⟨2, by decide⟩),
   opAt 3172 .POP,
   opAt 3173 (.Dup ⟨1, by decide⟩),
   pushAt 3174 2 5120,
   opAt 3175 .ADD,
   opAt 3176 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3177 (.Dup ⟨0, by decide⟩),
   opAt 3178 .ISZERO,
   pushAt 3179 2 4521,
   opAt 3180 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3350 .JUMPDEST,
   opAt 3351 (.Dup ⟨0, by decide⟩),
   opAt 3352 .MLOAD,
   pushAt 3353 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3354 (.Dup ⟨5, by decide⟩),
   opAt 3355 (.Dup ⟨2, by decide⟩),
   opAt 3356 .MUL,
   opAt 3357 (.Swap ⟨1, by decide⟩),
   opAt 3358 (.Dup ⟨6, by decide⟩),
   opAt 3359 .MULMOD,
   opAt 3360 (.Dup ⟨1, by decide⟩),
   opAt 3361 (.Dup ⟨1, by decide⟩),
   opAt 3362 .LT,
   opAt 3363 .SUB,
   opAt 3364 (.Dup ⟨4, by decide⟩),
   opAt 3365 (.Dup ⟨2, by decide⟩),
   opAt 3366 .ADD,
   opAt 3367 (.Dup ⟨0, by decide⟩),
   opAt 3368 (.Swap ⟨5, by decide⟩),
   opAt 3369 .GT,
   opAt 3370 .SUB,
   opAt 3371 .SUB,
   opAt 3372 (.Dup ⟨3, by decide⟩),
   opAt 3373 (.Dup ⟨3, by decide⟩),
   opAt 3374 .MLOAD,
   opAt 3375 .ADD,
   opAt 3376 (.Dup ⟨0, by decide⟩),
   opAt 3377 (.Swap ⟨4, by decide⟩),
   opAt 3378 .GT,
   opAt 3379 .ADD,
   opAt 3380 (.Swap ⟨2, by decide⟩),
   opAt 3381 (.Dup ⟨2, by decide⟩),
   pushAt 3382 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3383 .ADD,
   opAt 3384 (.Swap ⟨2, by decide⟩),
   opAt 3385 .MSTORE,
   pushAt 3386 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3387 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3388 2 8224,
   opAt 3389 (.Dup ⟨2, by decide⟩),
   opAt 3390 .GT,
   pushAt 3391 2 4738,
   opAt 3392 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3425 .JUMPDEST,
   opAt 3426 (.Dup ⟨0, by decide⟩),
   opAt 3427 .MLOAD,
   opAt 3428 (.Dup ⟨1, by decide⟩),
   pushAt 3429 2 8256,
   opAt 3430 (.Swap ⟨0, by decide⟩),
   opAt 3431 .SUB,
   opAt 3432 .MLOAD,
   opAt 3433 (.Dup ⟨1, by decide⟩),
   opAt 3434 .ADD,
   opAt 3435 (.Dup ⟨0, by decide⟩),
   opAt 3436 (.Dup ⟨2, by decide⟩),
   opAt 3437 .GT,
   opAt 3438 (.Swap ⟨1, by decide⟩),
   opAt 3439 .POP,
   opAt 3440 (.Dup ⟨3, by decide⟩),
   opAt 3441 .ADD,
   opAt 3442 (.Dup ⟨0, by decide⟩),
   opAt 3443 (.Dup ⟨4, by decide⟩),
   opAt 3444 .GT,
   opAt 3445 (.Swap ⟨3, by decide⟩),
   opAt 3446 .POP,
   opAt 3447 (.Dup ⟨2, by decide⟩),
   opAt 3448 .MSTORE,
   opAt 3449 (.Swap ⟨0, by decide⟩),
   opAt 3450 (.Swap ⟨1, by decide⟩),
   opAt 3451 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3452 (.Swap ⟨0, by decide⟩),
   pushAt 3453 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3454 .ADD,
   pushAt 3455 2 8255,
   opAt 3456 (.Dup ⟨1, by decide⟩),
   opAt 3457 .GT,
   pushAt 3458 2 4921,
   opAt 3459 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3481 .JUMPDEST,
   opAt 3482 (.Dup ⟨0, by decide⟩),
   opAt 3483 .MLOAD,
   opAt 3484 (.Dup ⟨1, by decide⟩),
   pushAt 3485 2 8256,
   opAt 3486 (.Swap ⟨0, by decide⟩),
   opAt 3487 .SUB,
   opAt 3488 .MLOAD,
   opAt 3489 (.Dup ⟨1, by decide⟩),
   opAt 3490 (.Dup ⟨1, by decide⟩),
   opAt 3491 .GT,
   opAt 3492 (.Swap ⟨1, by decide⟩),
   opAt 3493 .SUB,
   opAt 3494 (.Dup ⟨3, by decide⟩),
   opAt 3495 (.Dup ⟨1, by decide⟩),
   opAt 3496 .LT,
   opAt 3497 (.Swap ⟨0, by decide⟩),
   opAt 3498 (.Dup ⟨4, by decide⟩),
   opAt 3499 (.Swap ⟨0, by decide⟩),
   opAt 3500 .SUB,
   opAt 3501 (.Dup ⟨3, by decide⟩),
   opAt 3502 .MSTORE,
   opAt 3503 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3504 (.Swap ⟨1, by decide⟩),
   opAt 3505 .POP,
   pushAt 3506 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3507 .ADD,
   pushAt 3508 2 8255,
   opAt 3509 (.Dup ⟨1, by decide⟩),
   opAt 3510 .GT,
   pushAt 3511 2 5027,
   opAt 3512 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
