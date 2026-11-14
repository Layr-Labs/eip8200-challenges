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
  [opAt 2508 .JUMPDEST,
   opAt 2509 (.Dup ⟨0,by decide⟩),
   opAt 2510 .MLOAD,
   pushAt 2511 2 2112,
   opAt 2512 (.Dup ⟨2,by decide⟩),
   opAt 2513 .SUB,
   opAt 2514 .MLOAD,
   opAt 2515 (.Dup ⟨1,by decide⟩),
   opAt 2516 .ADD,
   opAt 2517 (.Swap ⟨0,by decide⟩),
   opAt 2518 (.Dup ⟨1,by decide⟩),
   opAt 2519 .LT,
   opAt 2520 (.Swap ⟨0,by decide⟩),
   opAt 2521 (.Dup ⟨3,by decide⟩),
   opAt 2522 .ADD,
   opAt 2523 (.Swap ⟨2,by decide⟩),
   opAt 2524 (.Dup ⟨3,by decide⟩),
   opAt 2525 .LT,
   opAt 2526 .OR,
   opAt 2527 (.Swap ⟨1,by decide⟩),
   opAt 2528 (.Dup ⟨1,by decide⟩),
   opAt 2529 .MSTORE]
/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2530 1 31,
   opAt 2531 .NOT,
   opAt 2532 .ADD,
   pushAt 2533 2 2111,
   opAt 2534 (.Dup ⟨1,by decide⟩),
   opAt 2535 .GT,
   pushAt 2536 2 3219,
   opAt 2537 .JUMPI]
/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []
end CycleSubmission.Global.Fast
