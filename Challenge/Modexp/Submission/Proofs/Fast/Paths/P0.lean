import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 0 (instructions 977..1027). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 977..985, pc 1314..1326. -/
def blk977 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 494 .JUMPDEST,
   pushAt 495 1 64,
   opAt 496 .CALLDATALOAD,
   opAt 497 .JUMPDEST,
   pushAt 498 1 33,
   opAt 499 (.Dup ⟨1, by decide⟩),
   opAt 500 .SUB,
   pushAt 501 1 223,
   opAt 502 .LT,
   pushAt 503 2 1170,
   opAt 504 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 505 1 32,
   opAt 506 .CALLDATALOAD,
   pushAt 507 0 0,
   opAt 508 .CALLDATALOAD]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 509 (.Dup ⟨2, by decide⟩),
   pushAt 510 1 31,
   opAt 511 .ADD,
   pushAt 512 1 5,
   opAt 513 .SHR,
   opAt 514 (.Dup ⟨0, by decide⟩),
   pushAt 515 1 5,
   opAt 516 .SHL,
   opAt 517 (.Dup ⟨3, by decide⟩),
   opAt 518 (.Dup ⟨3, by decide⟩),
   opAt 519 .ADD,
   pushAt 520 1 96,
   opAt 521 .ADD,
   opAt 522 (.Dup ⟨5, by decide⟩),
   opAt 523 (.Dup ⟨2, by decide⟩),
   opAt 524 .SUB,
   pushAt 525 1 3,
   opAt 526 .SHL,
   opAt 527 (.Dup ⟨1, by decide⟩),
   opAt 528 .CALLDATALOAD,
   opAt 529 (.Swap ⟨0, by decide⟩),
   opAt 530 .SHR,
   opAt 531 .ISZERO,
   pushAt 532 2 1176,
   opAt 533 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
