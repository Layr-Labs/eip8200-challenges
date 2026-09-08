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
  [opAt 3131 .JUMPDEST,
   opAt 3132 (.Dup ⟨0, by decide⟩),
   opAt 3133 .MLOAD,
   opAt 3134 .NOT,
   opAt 3135 (.Dup ⟨2, by decide⟩),
   opAt 3136 .ADD,
   opAt 3137 (.Dup ⟨2, by decide⟩),
   opAt 3138 (.Dup ⟨1, by decide⟩),
   opAt 3139 .LT,
   opAt 3140 (.Swap ⟨2, by decide⟩),
   opAt 3141 .POP,
   opAt 3142 (.Dup ⟨1, by decide⟩),
   pushAt 3143 2 5120,
   opAt 3144 .ADD,
   opAt 3145 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3146 (.Dup ⟨0, by decide⟩),
   opAt 3147 .ISZERO,
   pushAt 3148 2 4803,
   opAt 3149 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3320 .JUMPDEST,
   opAt 3321 (.Dup ⟨3, by decide⟩),
   opAt 3322 (.Dup ⟨1, by decide⟩),
   opAt 3323 .MLOAD,
   opAt 3324 (.Dup ⟨1, by decide⟩),
   opAt 3325 (.Dup ⟨1, by decide⟩),
   opAt 3326 .MUL,
   opAt 3327 (.Swap ⟨1, by decide⟩),
   pushAt 3328 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3329 (.Swap ⟨1, by decide⟩),
   opAt 3330 .MULMOD,
   opAt 3331 (.Dup ⟨1, by decide⟩),
   opAt 3332 (.Dup ⟨1, by decide⟩),
   opAt 3333 .LT,
   opAt 3334 (.Dup ⟨2, by decide⟩),
   opAt 3335 .ADD,
   opAt 3336 (.Swap ⟨0, by decide⟩),
   opAt 3337 .SUB,
   opAt 3338 (.Dup ⟨3, by decide⟩),
   opAt 3339 .MLOAD,
   opAt 3340 (.Swap ⟨1, by decide⟩),
   opAt 3341 (.Dup ⟨2, by decide⟩),
   opAt 3342 .ADD,
   opAt 3343 (.Swap ⟨1, by decide⟩),
   opAt 3344 (.Dup ⟨2, by decide⟩),
   opAt 3345 .LT,
   opAt 3346 .ADD,
   opAt 3347 (.Swap ⟨0, by decide⟩),
   opAt 3348 (.Dup ⟨4, by decide⟩),
   opAt 3349 .ADD,
   opAt 3350 (.Swap ⟨3, by decide⟩),
   opAt 3351 (.Dup ⟨4, by decide⟩),
   opAt 3352 .LT,
   opAt 3353 .ADD,
   opAt 3354 (.Swap ⟨2, by decide⟩),
   opAt 3355 (.Dup ⟨2, by decide⟩),
   opAt 3356 .MSTORE,
   pushAt 3357 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3358 .ADD,
   opAt 3359 (.Swap ⟨0, by decide⟩),
   pushAt 3360 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3361 .ADD,
   opAt 3362 (.Swap ⟨0, by decide⟩)]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3363 2 8224,
   opAt 3364 (.Dup ⟨2, by decide⟩),
   opAt 3365 .GT,
   pushAt 3366 2 5021,
   opAt 3367 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3400 .JUMPDEST,
   opAt 3401 (.Dup ⟨0, by decide⟩),
   opAt 3402 .MLOAD,
   opAt 3403 (.Dup ⟨1, by decide⟩),
   pushAt 3404 2 8256,
   opAt 3405 (.Swap ⟨0, by decide⟩),
   opAt 3406 .SUB,
   opAt 3407 .MLOAD,
   opAt 3408 (.Dup ⟨1, by decide⟩),
   opAt 3409 .ADD,
   opAt 3410 (.Dup ⟨0, by decide⟩),
   opAt 3411 (.Dup ⟨2, by decide⟩),
   opAt 3412 .GT,
   opAt 3413 (.Swap ⟨1, by decide⟩),
   opAt 3414 .POP,
   opAt 3415 (.Dup ⟨3, by decide⟩),
   opAt 3416 .ADD,
   opAt 3417 (.Dup ⟨0, by decide⟩),
   opAt 3418 (.Dup ⟨4, by decide⟩),
   opAt 3419 .GT,
   opAt 3420 (.Swap ⟨3, by decide⟩),
   opAt 3421 .POP,
   opAt 3422 (.Dup ⟨2, by decide⟩),
   opAt 3423 .MSTORE,
   opAt 3424 (.Swap ⟨0, by decide⟩),
   opAt 3425 (.Swap ⟨1, by decide⟩),
   opAt 3426 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3427 (.Swap ⟨0, by decide⟩),
   pushAt 3428 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3429 .ADD,
   pushAt 3430 2 8255,
   opAt 3431 (.Dup ⟨1, by decide⟩),
   opAt 3432 .GT,
   pushAt 3433 2 5209,
   opAt 3434 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3456 .JUMPDEST,
   opAt 3457 (.Dup ⟨0, by decide⟩),
   opAt 3458 .MLOAD,
   opAt 3459 (.Dup ⟨1, by decide⟩),
   pushAt 3460 2 8256,
   opAt 3461 (.Swap ⟨0, by decide⟩),
   opAt 3462 .SUB,
   opAt 3463 .MLOAD,
   opAt 3464 (.Dup ⟨1, by decide⟩),
   opAt 3465 (.Dup ⟨1, by decide⟩),
   opAt 3466 .GT,
   opAt 3467 (.Swap ⟨1, by decide⟩),
   opAt 3468 .SUB,
   opAt 3469 (.Dup ⟨3, by decide⟩),
   opAt 3470 (.Dup ⟨1, by decide⟩),
   opAt 3471 .LT,
   opAt 3472 (.Swap ⟨0, by decide⟩),
   opAt 3473 (.Dup ⟨4, by decide⟩),
   opAt 3474 (.Swap ⟨0, by decide⟩),
   opAt 3475 .SUB,
   opAt 3476 (.Dup ⟨3, by decide⟩),
   opAt 3477 .MSTORE,
   opAt 3478 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3479 (.Swap ⟨1, by decide⟩),
   opAt 3480 .POP,
   pushAt 3481 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3482 .ADD,
   pushAt 3483 2 8255,
   opAt 3484 (.Dup ⟨1, by decide⟩),
   opAt 3485 .GT,
   pushAt 3486 2 5315,
   opAt 3487 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
