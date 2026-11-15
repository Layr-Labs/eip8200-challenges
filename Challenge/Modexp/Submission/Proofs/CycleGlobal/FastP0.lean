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
  [opAt 389 .JUMPDEST,
   pushAt 390 1 64,
   opAt 391 .CALLDATALOAD,
   pushAt 392 1 33,
   opAt 393 (.Dup ⟨1,by decide⟩),
   opAt 394 .SUB,
   pushAt 395 1 223,
   opAt 396 .LT,
   pushAt 397 2 10322,
   opAt 398 .JUMPI]
/-- Instructions 986..989, pc 1133..1137.  The EIP-7834 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 399 1 32,
   opAt 400 .CALLDATALOAD,
   pushAt 401 0 0,
   opAt 402 .CALLDATALOAD]
/-- Instructions 417..455, pc 598..648: the top-limb, parity, width and Montgomery-inverse
checks, ORed into one `JUMPI` (the bail target is a `PUSH2` at 645 that absorbed the former
padding `JUMPDEST`). -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 403 1 31,
   opAt 404 (.Dup ⟨3,by decide⟩),
   opAt 405 .ADD,
   pushAt 406 1 5,
   opAt 407 .SHR,
   opAt 408 (.Dup ⟨0,by decide⟩),
   pushAt 409 1 5,
   opAt 410 .SHL,
   pushAt 411 1 96,
   opAt 412 (.Dup ⟨3,by decide⟩),
   opAt 413 .ADD,
   opAt 414 (.Dup ⟨4,by decide⟩),
   opAt 415 .ADD,
   opAt 416 (.Dup ⟨0,by decide⟩),
   opAt 417 .CALLDATALOAD,
   pushAt 418 0 0,
   opAt 419 .SGT,
   opAt 420 .ISZERO,
   pushAt 421 1 32,
   opAt 422 (.Dup ⟨7,by decide⟩),
   opAt 423 (.Dup ⟨3,by decide⟩),
   opAt 424 .ADD,
   opAt 425 .SUB,
   opAt 426 .CALLDATALOAD,
   opAt 427 .NOT,
   opAt 428 (.Dup ⟨0,by decide⟩),
   pushAt 429 0 0,
   opAt 430 .SUB,
   opAt 431 .AND,
   pushAt 432 1 2,
   opAt 433 .GT,
   opAt 434 (.Dup ⟨7,by decide⟩),
   pushAt 435 1 127,
   opAt 436 .AND,
   opAt 437 .OR,
   opAt 438 .OR,
   pushAt 439 1 174,
   opAt 440 .JUMPI]
end CycleSubmission.Global.Fast
