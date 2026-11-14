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
  [opAt 2507 .JUMPDEST,
   opAt 2508 (.Dup ⟨0,by decide⟩),
   opAt 2509 .MLOAD,
   pushAt 2510 2 2112,
   opAt 2511 (.Dup ⟨2,by decide⟩),
   opAt 2512 .SUB,
   opAt 2513 .MLOAD,
   opAt 2514 (.Dup ⟨1,by decide⟩),
   opAt 2515 .ADD,
   opAt 2516 (.Swap ⟨0,by decide⟩),
   opAt 2517 (.Dup ⟨1,by decide⟩),
   opAt 2518 .LT,
   opAt 2519 (.Swap ⟨0,by decide⟩),
   opAt 2520 (.Dup ⟨3,by decide⟩),
   opAt 2521 .ADD,
   opAt 2522 (.Swap ⟨2,by decide⟩),
   opAt 2523 (.Dup ⟨3,by decide⟩),
   opAt 2524 .LT,
   opAt 2525 .OR,
   opAt 2526 (.Swap ⟨1,by decide⟩),
   opAt 2527 (.Dup ⟨1,by decide⟩),
   opAt 2528 .MSTORE]
/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2529 1 31,
   opAt 2530 .NOT,
   opAt 2531 .ADD,
   pushAt 2532 2 2111,
   opAt 2533 (.Dup ⟨1,by decide⟩),
   opAt 2534 .GT,
   pushAt 2535 2 3218,
   opAt 2536 .JUMPI]
/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []
end CycleSubmission.Global.Fast
