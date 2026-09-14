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
  [opAt 421 .JUMPDEST,
   pushAt 422 1 64,
   opAt 423 .CALLDATALOAD,
   pushAt 424 1 33,
   opAt 425 (.Dup ⟨1, by decide⟩),
   opAt 426 .SUB,
   pushAt 427 1 223,
   opAt 428 .LT,
   pushAt 429 2 1047,
   opAt 430 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 431 1 32,
   opAt 432 .CALLDATALOAD,
   pushAt 433 0 0,
   opAt 434 .CALLDATALOAD]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 435 1 31,
   opAt 436 (.Dup ⟨3, by decide⟩),
   opAt 437 .ADD,
   pushAt 438 1 5,
   opAt 439 .SHR,
   opAt 440 (.Dup ⟨0, by decide⟩),
   pushAt 441 1 5,
   opAt 442 .SHL,
   pushAt 443 1 96,
   opAt 444 (.Dup ⟨3, by decide⟩),
   opAt 445 .ADD,
   opAt 446 (.Dup ⟨4, by decide⟩),
   opAt 447 .ADD,
   opAt 448 (.Dup ⟨0, by decide⟩),
   opAt 449 .CALLDATALOAD,
   opAt 450 (.Dup ⟨6, by decide⟩),
   opAt 451 (.Dup ⟨3, by decide⟩),
   opAt 452 .SUB,
   pushAt 453 1 3,
   opAt 454 .SHL,
   opAt 455 .SHR,
   opAt 456 .ISZERO,
   pushAt 457 2 1053,
   opAt 458 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
