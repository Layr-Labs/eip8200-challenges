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
  [opAt 392 .JUMPDEST,
   pushAt 393 1 64,
   opAt 394 .CALLDATALOAD,
   pushAt 395 1 33,
   opAt 396 (.Dup ⟨1,by decide⟩),
   opAt 397 .SUB,
   pushAt 398 1 223,
   opAt 399 .LT,
   pushAt 400 2 3481,
   opAt 401 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 402 1 32,
   opAt 403 .CALLDATALOAD,
   pushAt 404 0 0,
   opAt 405 .CALLDATALOAD]

/-- Instructions 417..455, pc 598..648: the top-limb, parity, width and Montgomery-inverse
checks, ORed into one `JUMPI` (the bail target is a `PUSH2` at 645 that absorbed the former
padding `JUMPDEST`). -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 406 1 31,
   opAt 407 (.Dup ⟨3,by decide⟩),
   opAt 408 .ADD,
   pushAt 409 1 5,
   opAt 410 .SHR,
   opAt 411 (.Dup ⟨0,by decide⟩),
   pushAt 412 1 5,
   opAt 413 .SHL,
   pushAt 414 1 96,
   opAt 415 (.Dup ⟨3,by decide⟩),
   opAt 416 .ADD,
   opAt 417 (.Dup ⟨4,by decide⟩),
   opAt 418 .ADD,
   opAt 419 (.Dup ⟨0,by decide⟩),
   opAt 420 .CALLDATALOAD,
   pushAt 421 0 0,
   opAt 422 .SGT,
   opAt 423 .ISZERO,
   pushAt 424 1 32,
   opAt 425 (.Dup ⟨7,by decide⟩),
   opAt 426 (.Dup ⟨3,by decide⟩),
   opAt 427 .ADD,
   opAt 428 .SUB,
   opAt 429 .CALLDATALOAD,
   opAt 430 .NOT,
   opAt 431 (.Dup ⟨0,by decide⟩),
   pushAt 432 0 0,
   opAt 433 .SUB,
   opAt 434 .AND,
   pushAt 435 1 2,
   opAt 436 .GT,
   opAt 437 (.Dup ⟨7,by decide⟩),
   pushAt 438 1 127,
   opAt 439 .AND,
   opAt 440 .OR,
   opAt 441 .OR,
   pushAt 442 1 207,
   opAt 443 .JUMPI]

end CycleSubmission.Global.Fast
