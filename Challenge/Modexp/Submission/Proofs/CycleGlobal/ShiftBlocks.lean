import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftPaths
open CycleSubmission.SharedStackArgs
noncomputable section
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Loop-body blocks of the shift-reduce routine split before their exit tests, so
that each block reduction stays small enough for the kernel. -/
namespace CycleSubmission.Global.Fast
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2519 .JUMPDEST,
   opAt 2520 (.Dup dA0),
   opAt 2521 .MLOAD,
   pushAt 2522 2 2112,
   opAt 2523 (.Dup dA2),
   opAt 2524 .SUB,
   opAt 2525 .MLOAD,
   opAt 2526 (.Dup dA1),
   opAt 2527 .ADD,
   opAt 2528 (.Swap sA0),
   opAt 2529 (.Dup dA1),
   opAt 2530 .LT,
   opAt 2531 (.Swap sA0),
   opAt 2532 (.Dup dA3),
   opAt 2533 .ADD,
   opAt 2534 (.Swap sA2),
   opAt 2535 (.Dup dA3),
   opAt 2536 .LT,
   opAt 2537 .OR,
   opAt 2538 (.Swap sA1),
   opAt 2539 (.Dup dA1),
   opAt 2540 .MSTORE]
/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2541 1 31,
   opAt 2542 .NOT,
   opAt 2543 .ADD,
   pushAt 2544 2 2111,
   opAt 2545 (.Dup dA1),
   opAt 2546 .GT,
   pushAt 2547 2 3231,
   opAt 2548 .JUMPI]
/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []
end CycleSubmission.Global.Fast
