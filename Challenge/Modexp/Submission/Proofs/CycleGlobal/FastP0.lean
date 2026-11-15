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
  [opAt 598 .JUMPDEST,
   pushAt 599 1 64,
   opAt 600 .CALLDATALOAD,
   pushAt 601 1 33,
   opAt 602 (.Dup ⟨1,by decide⟩),
   opAt 603 .SUB,
   pushAt 604 1 223,
   opAt 605 .LT,
   pushAt 606 2 10876,
   opAt 607 .JUMPI]
/-- Instructions 986..989, pc 1133..1137.  The EIP-5834 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 608 1 32,
   opAt 609 .CALLDATALOAD,
   pushAt 610 0 0,
   opAt 611 .CALLDATALOAD]
/-- Instructions 417..455, pc 598..648: the top-limb, parity, width and Montgomery-inverse
checks, ORed into one `JUMPI` (the bail target is a `PUSH2` at 645 that absorbed the former
padding `JUMPDEST`). -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 612 1 31,
   opAt 613 (.Dup ⟨3,by decide⟩),
   opAt 614 .ADD,
   pushAt 615 1 5,
   opAt 616 .SHR,
   opAt 617 (.Dup ⟨0,by decide⟩),
   pushAt 618 1 5,
   opAt 619 .SHL,
   pushAt 620 1 96,
   opAt 621 (.Dup ⟨3,by decide⟩),
   opAt 622 .ADD,
   opAt 623 (.Dup ⟨4,by decide⟩),
   opAt 624 .ADD,
   opAt 625 (.Dup ⟨0,by decide⟩),
   opAt 626 .CALLDATALOAD,
   pushAt 627 0 0,
   opAt 628 .SGT,
   opAt 629 .ISZERO,
   pushAt 630 1 32,
   opAt 631 (.Dup ⟨7,by decide⟩),
   opAt 632 (.Dup ⟨3,by decide⟩),
   opAt 633 .ADD,
   opAt 634 .SUB,
   opAt 635 .CALLDATALOAD,
   opAt 636 .NOT,
   opAt 637 (.Dup ⟨0,by decide⟩),
   pushAt 638 0 0,
   opAt 639 .SUB,
   opAt 640 .AND,
   pushAt 641 1 2,
   opAt 642 .GT,
   opAt 643 (.Dup ⟨7,by decide⟩),
   pushAt 644 1 127,
   opAt 645 .AND,
   opAt 646 .OR,
   opAt 647 .OR,
   pushAt 648 1 172,
   opAt 649 .JUMPI]
end CycleSubmission.Global.Fast
