import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 0 (instructions 977..1027). -/

namespace CycleSubmission.Global.Fast
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 977..985, pc 1314..1326. -/
def blk977 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 403 .JUMPDEST,
   pushAt 404 1 64,
   opAt 405 .CALLDATALOAD,
   pushAt 406 1 33,
   opAt 407 (.Dup ⟨1, by decide⟩),
   opAt 408 .SUB,
   pushAt 409 1 223,
   opAt 410 .LT,
   pushAt 411 2 697,
   opAt 412 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 413 1 32,
   opAt 414 .CALLDATALOAD,
   pushAt 415 0 0,
   opAt 416 .CALLDATALOAD]

/-- Instructions 417..455, pc 598..648: the top-limb, parity, width and Montgomery-inverse
checks, ORed into one `JUMPI` (the `JUMPDEST` at 645 is padding that keeps the layout). -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 417 1 31,
   opAt 418 (.Dup ⟨3, by decide⟩),
   opAt 419 .ADD,
   pushAt 420 1 5,
   opAt 421 .SHR,
   opAt 422 (.Dup ⟨0, by decide⟩),
   pushAt 423 1 5,
   opAt 424 .SHL,
   pushAt 425 1 96,
   opAt 426 (.Dup ⟨3, by decide⟩),
   opAt 427 .ADD,
   opAt 428 (.Dup ⟨4, by decide⟩),
   opAt 429 .ADD,
   opAt 430 (.Dup ⟨0, by decide⟩),
   opAt 431 .CALLDATALOAD,
   pushAt 432 1 255,
   opAt 433 .SHR,
   opAt 434 .ISZERO,
   pushAt 435 2 32,
   opAt 436 (.Dup ⟨7, by decide⟩),
   opAt 437 (.Dup ⟨3, by decide⟩),
   opAt 438 .ADD,
   opAt 439 .SUB,
   opAt 440 .CALLDATALOAD,
   opAt 441 .NOT,
   opAt 442 (.Dup ⟨0, by decide⟩),
   opAt 443 .ISZERO,
   opAt 444 (.Swap ⟨0, by decide⟩),
   pushAt 445 2 1,
   opAt 446 .AND,
   opAt 447 .OR,
   opAt 448 (.Dup ⟨7, by decide⟩),
   pushAt 449 2 127,
   opAt 450 .AND,
   opAt 451 .OR,
   opAt 452 .OR,
   opAt 453 .JUMPDEST,
   pushAt 454 1 219,
   opAt 455 .JUMPI]

end CycleSubmission.Global.Fast
