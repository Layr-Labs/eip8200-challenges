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
  [opAt 406 .JUMPDEST,
   pushAt 407 1 64,
   opAt 408 .CALLDATALOAD,
   pushAt 409 1 33,
   opAt 410 (.Dup ⟨1, by decide⟩),
   opAt 411 .SUB,
   pushAt 412 1 223,
   opAt 413 .LT,
   pushAt 414 2 697,
   opAt 415 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 416 1 32,
   opAt 417 .CALLDATALOAD,
   pushAt 418 0 0,
   opAt 419 .CALLDATALOAD]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 420 1 31,
   opAt 421 (.Dup ⟨3, by decide⟩),
   opAt 422 .ADD,
   pushAt 423 1 5,
   opAt 424 .SHR,
   opAt 425 (.Dup ⟨0, by decide⟩),
   pushAt 426 1 5,
   opAt 427 .SHL,
   pushAt 428 1 96,
   opAt 429 (.Dup ⟨3, by decide⟩),
   opAt 430 .ADD,
   opAt 431 (.Dup ⟨4, by decide⟩),
   opAt 432 .ADD,
   opAt 433 (.Dup ⟨0, by decide⟩),
   opAt 434 .CALLDATALOAD,
   pushAt 435 1 255,
   opAt 436 .SHR,
   opAt 437 .ISZERO,
   pushAt 438 1 219,
   opAt 439 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
