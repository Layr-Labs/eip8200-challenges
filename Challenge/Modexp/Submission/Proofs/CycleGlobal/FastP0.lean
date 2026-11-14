import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
open CycleSubmission.SharedStackArgs

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
  [opAt 391 .JUMPDEST,
   pushAt 392 1 64,
   opAt 393 .CALLDATALOAD,
   pushAt 394 1 33,
   opAt 395 (.Dup dA1),
   opAt 396 .SUB,
   pushAt 397 1 223,
   opAt 398 .LT,
   pushAt 399 2 9532,
   opAt 400 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 401 1 32,
   opAt 402 .CALLDATALOAD,
   pushAt 403 0 0,
   opAt 404 .CALLDATALOAD]

/-- Instructions 417..455, pc 598..648: the top-limb, parity, width and Montgomery-inverse
checks, ORed into one `JUMPI` (the bail target is a `PUSH2` at 645 that absorbed the former
padding `JUMPDEST`). -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 405 1 31,
   opAt 406 (.Dup dA3),
   opAt 407 .ADD,
   pushAt 408 1 5,
   opAt 409 .SHR,
   opAt 410 (.Dup dA0),
   pushAt 411 1 5,
   opAt 412 .SHL,
   pushAt 413 1 96,
   opAt 414 (.Dup dA3),
   opAt 415 .ADD,
   opAt 416 (.Dup dA4),
   opAt 417 .ADD,
   opAt 418 (.Dup dA0),
   opAt 419 .CALLDATALOAD,
   pushAt 420 0 0,
   opAt 421 .SGT,
   opAt 422 .ISZERO,
   pushAt 423 1 32,
   opAt 424 (.Dup dA7),
   opAt 425 (.Dup dA3),
   opAt 426 .ADD,
   opAt 427 .SUB,
   opAt 428 .CALLDATALOAD,
   opAt 429 .NOT,
   opAt 430 (.Dup dA0),
   pushAt 431 0 0,
   opAt 432 .SUB,
   opAt 433 .AND,
   pushAt 434 1 2,
   opAt 435 .GT,
   opAt 436 (.Dup dA7),
   pushAt 437 1 127,
   opAt 438 .AND,
   opAt 439 .OR,
   opAt 440 .OR,
   pushAt 441 1 207,
   opAt 442 .JUMPI]

end CycleSubmission.Global.Fast
