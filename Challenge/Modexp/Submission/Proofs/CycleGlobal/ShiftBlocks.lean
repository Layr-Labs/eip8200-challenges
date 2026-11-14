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
  [opAt 2511 .JUMPDEST,
   opAt 2512 (.Dup ⟨0,by decide⟩),
   opAt 2513 .MLOAD,
   pushAt 2514 2 2112,
   opAt 2515 (.Dup ⟨2,by decide⟩),
   opAt 2516 .SUB,
   opAt 2517 .MLOAD,
   opAt 2518 (.Dup ⟨1,by decide⟩),
   opAt 2519 .ADD,
   opAt 2520 (.Swap ⟨0,by decide⟩),
   opAt 2521 (.Dup ⟨1,by decide⟩),
   opAt 2522 .LT,
   opAt 2523 (.Swap ⟨0,by decide⟩),
   opAt 2524 (.Dup ⟨3,by decide⟩),
   opAt 2525 .ADD,
   opAt 2526 (.Swap ⟨2,by decide⟩),
   opAt 2527 (.Dup ⟨3,by decide⟩),
   opAt 2528 .LT,
   opAt 2529 .OR,
   opAt 2530 (.Swap ⟨1,by decide⟩),
   opAt 2531 (.Dup ⟨1,by decide⟩),
   opAt 2532 .MSTORE]
/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2533 1 31,
   opAt 2534 .NOT,
   opAt 2535 .ADD,
   pushAt 2536 2 2111,
   opAt 2537 (.Dup ⟨1,by decide⟩),
   opAt 2538 .GT,
   pushAt 2539 2 3221,
   opAt 2540 .JUMPI]
/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []
end CycleSubmission.Global.Fast
