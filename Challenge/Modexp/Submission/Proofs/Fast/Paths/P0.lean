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
  [opAt 423 .JUMPDEST,
   pushAt 424 1 64,
   opAt 425 .CALLDATALOAD,
   pushAt 426 1 33,
   opAt 427 (.Dup ⟨1, by decide⟩),
   opAt 428 .SUB,
   pushAt 429 1 223,
   opAt 430 .LT,
   pushAt 431 2 794,
   opAt 432 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 433 1 32,
   opAt 434 .CALLDATALOAD,
   pushAt 435 0 0,
   opAt 436 .CALLDATALOAD]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 437 1 31,
   opAt 438 (.Dup ⟨3, by decide⟩),
   opAt 439 .ADD,
   pushAt 440 1 5,
   opAt 441 .SHR,
   opAt 442 (.Dup ⟨0, by decide⟩),
   pushAt 443 1 5,
   opAt 444 .SHL,
   pushAt 445 1 96,
   opAt 446 (.Dup ⟨3, by decide⟩),
   opAt 447 .ADD,
   opAt 448 (.Dup ⟨4, by decide⟩),
   opAt 449 .ADD,
   opAt 450 (.Dup ⟨0, by decide⟩),
   opAt 451 .CALLDATALOAD,
   pushAt 452 1 255,
   opAt 453 .SHR,
   opAt 454 .JUMPDEST,
   opAt 455 .JUMPDEST,
   opAt 456 .JUMPDEST,
   opAt 457 .JUMPDEST,
   opAt 458 .ISZERO,
   pushAt 459 2 800,
   opAt 460 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
