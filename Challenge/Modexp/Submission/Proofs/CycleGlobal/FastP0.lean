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
  [opAt 400 .JUMPDEST,
   pushAt 401 1 64,
   opAt 402 .CALLDATALOAD,
   pushAt 403 1 33,
   opAt 404 (.Dup ⟨1, by decide⟩),
   opAt 405 .SUB,
   pushAt 406 1 223,
   opAt 407 .LT,
   pushAt 408 2 3640,
   opAt 409 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 410 1 32,
   opAt 411 .CALLDATALOAD,
   pushAt 412 0 0,
   opAt 413 .CALLDATALOAD]

/-- Instructions 417..455, pc 598..648: the top-limb, parity, width and Montgomery-inverse
checks, ORed into one `JUMPI` (the bail target is a `PUSH2` at 645 that absorbed the former
padding `JUMPDEST`). -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 414 1 31,
   opAt 415 (.Dup ⟨3, by decide⟩),
   opAt 416 .ADD,
   pushAt 417 1 5,
   opAt 418 .SHR,
   opAt 419 (.Dup ⟨0, by decide⟩),
   pushAt 420 1 5,
   opAt 421 .SHL,
   pushAt 422 1 96,
   opAt 423 (.Dup ⟨3, by decide⟩),
   opAt 424 .ADD,
   opAt 425 (.Dup ⟨4, by decide⟩),
   opAt 426 .ADD,
   opAt 427 (.Dup ⟨0, by decide⟩),
   opAt 428 .CALLDATALOAD,
   pushAt 429 1 255,
   opAt 430 .SHR,
   opAt 431 .ISZERO,
   pushAt 432 2 32,
   opAt 433 (.Dup ⟨7, by decide⟩),
   opAt 434 (.Dup ⟨3, by decide⟩),
   opAt 435 .ADD,
   opAt 436 .SUB,
   opAt 437 .CALLDATALOAD,
   opAt 438 .NOT,
   opAt 439 (.Dup ⟨0, by decide⟩),
   opAt 440 .ISZERO,
   opAt 441 (.Swap ⟨0, by decide⟩),
   pushAt 442 2 1,
   opAt 443 .AND,
   opAt 444 .OR,
   opAt 445 (.Dup ⟨7, by decide⟩),
   pushAt 446 2 127,
   opAt 447 .AND,
   opAt 448 .OR,
   opAt 449 .OR,
   pushAt 450 2 219,
   opAt 451 .JUMPI]

end CycleSubmission.Global.Fast
