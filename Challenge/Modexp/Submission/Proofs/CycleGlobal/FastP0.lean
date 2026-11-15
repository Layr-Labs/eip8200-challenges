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
  [opAt 564 .JUMPDEST,
   pushAt 565 1 64,
   opAt 566 .CALLDATALOAD,
   pushAt 567 1 33,
   opAt 568 (.Dup ⟨1,by decide⟩),
   opAt 569 .SUB,
   pushAt 570 1 223,
   opAt 571 .LT,
   pushAt 572 2 10563,
   opAt 573 .JUMPI]
/-- Instructions 986..989, pc 1133..1137.  The EIP-7714 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 574 1 32,
   opAt 575 .CALLDATALOAD,
   pushAt 576 0 0,
   opAt 577 .CALLDATALOAD]
/-- Instructions 417..455, pc 598..648: the top-limb, parity, width and Montgomery-inverse
checks, ORed into one `JUMPI` (the bail target is a `PUSH2` at 645 that absorbed the former
padding `JUMPDEST`). -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 578 1 31,
   opAt 579 (.Dup ⟨3,by decide⟩),
   opAt 580 .ADD,
   pushAt 581 1 5,
   opAt 582 .SHR,
   opAt 583 (.Dup ⟨0,by decide⟩),
   pushAt 584 1 5,
   opAt 585 .SHL,
   pushAt 586 1 96,
   opAt 587 (.Dup ⟨3,by decide⟩),
   opAt 588 .ADD,
   opAt 589 (.Dup ⟨4,by decide⟩),
   opAt 590 .ADD,
   opAt 591 (.Dup ⟨0,by decide⟩),
   opAt 592 .CALLDATALOAD,
   pushAt 593 0 0,
   opAt 594 .SGT,
   opAt 595 .ISZERO,
   pushAt 596 1 32,
   opAt 597 (.Dup ⟨7,by decide⟩),
   opAt 598 (.Dup ⟨3,by decide⟩),
   opAt 599 .ADD,
   opAt 600 .SUB,
   opAt 601 .CALLDATALOAD,
   opAt 602 .NOT,
   opAt 603 (.Dup ⟨0,by decide⟩),
   pushAt 604 0 0,
   opAt 605 .SUB,
   opAt 606 .AND,
   pushAt 607 1 2,
   opAt 608 .GT,
   opAt 609 (.Dup ⟨7,by decide⟩),
   pushAt 610 1 127,
   opAt 611 .AND,
   opAt 612 .OR,
   opAt 613 .OR,
   pushAt 614 1 172,
   opAt 615 .JUMPI]
end CycleSubmission.Global.Fast
