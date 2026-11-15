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
  [opAt 386 .JUMPDEST,
   pushAt 387 1 64,
   opAt 388 .CALLDATALOAD,
   pushAt 389 1 33,
   opAt 390 (.Dup ⟨1,by decide⟩),
   opAt 391 .SUB,
   pushAt 392 1 223,
   opAt 393 .LT,
   pushAt 394 2 10322,
   opAt 395 .JUMPI]
/-- Instructions 986..989, pc 1133..1137.  The EIP-7834 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 396 1 32,
   opAt 397 .CALLDATALOAD,
   pushAt 398 0 0,
   opAt 399 .CALLDATALOAD]
/-- Instructions 417..455, pc 598..648: the top-limb, parity, width and Montgomery-inverse
checks, ORed into one `JUMPI` (the bail target is a `PUSH2` at 645 that absorbed the former
padding `JUMPDEST`). -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 400 1 31,
   opAt 401 (.Dup ⟨3,by decide⟩),
   opAt 402 .ADD,
   pushAt 403 1 5,
   opAt 404 .SHR,
   opAt 405 (.Dup ⟨0,by decide⟩),
   pushAt 406 1 5,
   opAt 407 .SHL,
   pushAt 408 1 96,
   opAt 409 (.Dup ⟨3,by decide⟩),
   opAt 410 .ADD,
   opAt 411 (.Dup ⟨4,by decide⟩),
   opAt 412 .ADD,
   opAt 413 (.Dup ⟨0,by decide⟩),
   opAt 414 .CALLDATALOAD,
   pushAt 415 0 0,
   opAt 416 .SGT,
   opAt 417 .ISZERO,
   pushAt 418 1 32,
   opAt 419 (.Dup ⟨7,by decide⟩),
   opAt 420 (.Dup ⟨3,by decide⟩),
   opAt 421 .ADD,
   opAt 422 .SUB,
   opAt 423 .CALLDATALOAD,
   opAt 424 .NOT,
   opAt 425 (.Dup ⟨0,by decide⟩),
   pushAt 426 0 0,
   opAt 427 .SUB,
   opAt 428 .AND,
   pushAt 429 1 2,
   opAt 430 .GT,
   opAt 431 (.Dup ⟨7,by decide⟩),
   pushAt 432 1 127,
   opAt 433 .AND,
   opAt 434 .OR,
   opAt 435 .OR,
   pushAt 436 1 203,
   opAt 437 .JUMPI]
end CycleSubmission.Global.Fast
