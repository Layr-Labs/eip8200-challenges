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
   pushAt 497 1 33,
   opAt 498 (.Dup ⟨1, by decide⟩),
   opAt 499 .SUB,
   pushAt 500 1 223,
   opAt 501 .LT,
   pushAt 502 2 1157,
   opAt 503 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 504 1 32,
   opAt 505 .CALLDATALOAD,
   pushAt 506 0 0,
   opAt 507 .CALLDATALOAD]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 508 1 31,
   opAt 509 (.Dup ⟨3, by decide⟩),
   opAt 510 .ADD,
   pushAt 511 1 5,
   opAt 512 .SHR,
   opAt 513 (.Dup ⟨0, by decide⟩),
   pushAt 514 1 5,
   opAt 515 .SHL,
   pushAt 516 1 96,
   opAt 517 (.Dup ⟨3, by decide⟩),
   opAt 518 .ADD,
   opAt 519 (.Dup ⟨4, by decide⟩),
   opAt 520 .ADD,
   opAt 521 (.Dup ⟨0, by decide⟩),
   opAt 522 .CALLDATALOAD,
   opAt 523 (.Dup ⟨6, by decide⟩),
   opAt 524 (.Dup ⟨3, by decide⟩),
   opAt 525 .SUB,
   pushAt 526 1 3,
   opAt 527 .SHL,
   opAt 528 .SHR,
   opAt 529 .ISZERO,
   pushAt 530 2 1163,
   opAt 531 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
