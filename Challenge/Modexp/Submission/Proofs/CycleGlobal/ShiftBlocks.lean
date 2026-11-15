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
  [opAt 2493 .JUMPDEST,
   opAt 2494 (.Dup ⟨0,by decide⟩),
   opAt 2495 .MLOAD,
   pushAt 2496 2 2112,
   opAt 2497 (.Dup ⟨2,by decide⟩),
   opAt 2498 .SUB,
   opAt 2499 .MLOAD,
   opAt 2500 (.Dup ⟨1,by decide⟩),
   opAt 2501 .ADD,
   opAt 2502 (.Swap ⟨0,by decide⟩),
   opAt 2503 (.Dup ⟨1,by decide⟩),
   opAt 2504 .LT,
   opAt 2505 (.Swap ⟨0,by decide⟩),
   opAt 2506 (.Dup ⟨3,by decide⟩),
   opAt 2507 .ADD,
   opAt 2508 (.Swap ⟨2,by decide⟩),
   opAt 2509 (.Dup ⟨3,by decide⟩),
   opAt 2510 .LT,
   opAt 2511 .OR,
   opAt 2512 (.Swap ⟨1,by decide⟩),
   opAt 2513 (.Dup ⟨1,by decide⟩),
   opAt 2514 .MSTORE]
/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2515 1 31,
   opAt 2516 .NOT,
   opAt 2517 .ADD,
   pushAt 2518 2 2111,
   opAt 2519 (.Dup ⟨1,by decide⟩),
   opAt 2520 .GT,
   pushAt 2521 2 3234,
   opAt 2522 .JUMPI]
/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2401 to 2405). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []
end CycleSubmission.Global.Fast
