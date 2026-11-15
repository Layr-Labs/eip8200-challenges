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
  [opAt 2386 .JUMPDEST,
   opAt 2387 (.Dup ⟨0,by decide⟩),
   opAt 2388 .MLOAD,
   pushAt 2389 2 2112,
   opAt 2390 (.Dup ⟨2,by decide⟩),
   opAt 2391 .SUB,
   opAt 2392 .MLOAD,
   opAt 2393 (.Dup ⟨1,by decide⟩),
   opAt 2394 .ADD,
   opAt 2395 (.Swap ⟨0,by decide⟩),
   opAt 2396 (.Dup ⟨1,by decide⟩),
   opAt 2397 .LT,
   opAt 2398 (.Swap ⟨0,by decide⟩),
   opAt 2399 (.Dup ⟨3,by decide⟩),
   opAt 2400 .ADD,
   opAt 2401 (.Swap ⟨2,by decide⟩),
   opAt 2402 (.Dup ⟨3,by decide⟩),
   opAt 2403 .LT,
   opAt 2404 .OR,
   opAt 2405 (.Swap ⟨1,by decide⟩),
   opAt 2406 (.Dup ⟨1,by decide⟩),
   opAt 2407 .MSTORE]
/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2408 1 31,
   opAt 2409 .NOT,
   opAt 2410 .ADD,
   pushAt 2411 2 2111,
   opAt 2412 (.Dup ⟨1,by decide⟩),
   opAt 2413 .GT,
   pushAt 2414 2 3114,
   opAt 2415 .JUMPI]
/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2645 to 2649). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []
end CycleSubmission.Global.Fast
