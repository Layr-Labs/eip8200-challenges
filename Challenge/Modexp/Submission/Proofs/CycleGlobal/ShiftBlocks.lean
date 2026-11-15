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
  [opAt 2491 .JUMPDEST,
   opAt 2492 (.Dup ⟨0,by decide⟩),
   opAt 2493 .MLOAD,
   pushAt 2494 2 2112,
   opAt 2495 (.Dup ⟨2,by decide⟩),
   opAt 2496 .SUB,
   opAt 2497 .MLOAD,
   opAt 2498 (.Dup ⟨1,by decide⟩),
   opAt 2499 .ADD,
   opAt 2500 (.Swap ⟨0,by decide⟩),
   opAt 2501 (.Dup ⟨1,by decide⟩),
   opAt 2502 .LT,
   opAt 2503 (.Swap ⟨0,by decide⟩),
   opAt 2504 (.Dup ⟨3,by decide⟩),
   opAt 2505 .ADD,
   opAt 2506 (.Swap ⟨2,by decide⟩),
   opAt 2507 (.Dup ⟨3,by decide⟩),
   opAt 2508 .LT,
   opAt 2509 .OR,
   opAt 2510 (.Swap ⟨1,by decide⟩),
   opAt 2511 (.Dup ⟨1,by decide⟩),
   opAt 2512 .MSTORE]
/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2513 1 31,
   opAt 2514 .NOT,
   opAt 2515 .ADD,
   pushAt 2516 2 2111,
   opAt 2517 (.Dup ⟨1,by decide⟩),
   opAt 2518 .GT,
   pushAt 2519 2 3234,
   opAt 2520 .JUMPI]
/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2401 to 2405). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []
end CycleSubmission.Global.Fast
