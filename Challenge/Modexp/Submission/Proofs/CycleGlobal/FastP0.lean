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
  [opAt 387 .JUMPDEST,
   pushAt 388 1 64,
   opAt 389 .CALLDATALOAD,
   pushAt 390 1 33,
   opAt 391 (.Dup ⟨1,by decide⟩),
   opAt 392 .SUB,
   pushAt 393 1 223,
   opAt 394 .LT,
   pushAt 395 2 10568,
   opAt 396 .JUMPI]
/-- Instructions 986..989, pc 1133..1137.  The EIP-8080 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 397 1 32,
   opAt 398 .CALLDATALOAD,
   pushAt 399 0 0,
   opAt 400 .CALLDATALOAD]
/-- Instructions 417..455, pc 598..648: the top-limb, parity, width and Montgomery-inverse
checks, ORed into one `JUMPI` (the bail target is a `PUSH2` at 645 that absorbed the former
padding `JUMPDEST`). -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 401 1 31,
   opAt 402 (.Dup ⟨3,by decide⟩),
   opAt 403 .ADD,
   pushAt 404 1 5,
   opAt 405 .SHR,
   opAt 406 (.Dup ⟨0,by decide⟩),
   pushAt 407 1 5,
   opAt 408 .SHL,
   pushAt 409 1 96,
   opAt 410 (.Dup ⟨3,by decide⟩),
   opAt 411 .ADD,
   opAt 412 (.Dup ⟨4,by decide⟩),
   opAt 413 .ADD,
   opAt 414 (.Dup ⟨0,by decide⟩),
   opAt 415 .CALLDATALOAD,
   pushAt 416 0 0,
   opAt 417 .SGT,
   opAt 418 .ISZERO,
   pushAt 419 1 32,
   opAt 420 (.Dup ⟨7,by decide⟩),
   opAt 421 (.Dup ⟨3,by decide⟩),
   opAt 422 .ADD,
   opAt 423 .SUB,
   opAt 424 .CALLDATALOAD,
   opAt 425 .NOT,
   opAt 426 (.Dup ⟨0,by decide⟩),
   pushAt 427 0 0,
   opAt 428 .SUB,
   opAt 429 .AND,
   pushAt 430 1 2,
   opAt 431 .GT,
   opAt 432 (.Dup ⟨7,by decide⟩),
   pushAt 433 1 127,
   opAt 434 .AND,
   opAt 435 .OR,
   opAt 436 .OR,
   pushAt 437 1 172,
   opAt 438 .JUMPI]
end CycleSubmission.Global.Fast
