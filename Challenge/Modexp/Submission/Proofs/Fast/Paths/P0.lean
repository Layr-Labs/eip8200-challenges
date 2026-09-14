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
  [opAt 496 .JUMPDEST,
   pushAt 497 1 64,
   opAt 498 .CALLDATALOAD,
   pushAt 499 1 33,
   opAt 500 (.Dup ⟨1, by decide⟩),
   opAt 501 .SUB,
   pushAt 502 1 223,
   opAt 503 .LT,
   pushAt 504 2 1158,
   opAt 505 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 506 1 32,
   opAt 507 .CALLDATALOAD,
   pushAt 508 0 0,
   opAt 509 .CALLDATALOAD]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 510 1 31,
   opAt 511 (.Dup ⟨3, by decide⟩),
   opAt 512 .ADD,
   pushAt 513 1 5,
   opAt 514 .SHR,
   opAt 515 (.Dup ⟨0, by decide⟩),
   pushAt 516 1 5,
   opAt 517 .SHL,
   pushAt 518 1 96,
   opAt 519 (.Dup ⟨3, by decide⟩),
   opAt 520 .ADD,
   opAt 521 (.Dup ⟨4, by decide⟩),
   opAt 522 .ADD,
   opAt 523 (.Dup ⟨0, by decide⟩),
   opAt 524 .CALLDATALOAD,
   opAt 525 (.Dup ⟨6, by decide⟩),
   opAt 526 (.Dup ⟨3, by decide⟩),
   opAt 527 .SUB,
   pushAt 528 1 3,
   opAt 529 .SHL,
   opAt 530 .SHR,
   opAt 531 .ISZERO,
   pushAt 532 2 1164,
   opAt 533 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
