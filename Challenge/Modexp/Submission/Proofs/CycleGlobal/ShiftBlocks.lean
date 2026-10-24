import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftPaths
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
  [opAt 2409 .JUMPDEST,
   opAt 2410 (.Dup ⟨0, by decide⟩),
   opAt 2411 .MLOAD,
   pushAt 2412 2 2112,
   opAt 2413 (.Dup ⟨2, by decide⟩),
   opAt 2414 .SUB,
   opAt 2415 .MLOAD,
   opAt 2416 (.Dup ⟨1, by decide⟩),
   opAt 2417 .ADD,
   opAt 2418 (.Swap ⟨0, by decide⟩),
   opAt 2419 (.Dup ⟨1, by decide⟩),
   opAt 2420 .LT,
   opAt 2421 (.Swap ⟨0, by decide⟩),
   opAt 2422 (.Dup ⟨3, by decide⟩),
   opAt 2423 .ADD,
   opAt 2424 (.Swap ⟨2, by decide⟩),
   opAt 2425 (.Dup ⟨3, by decide⟩),
   opAt 2426 .LT,
   opAt 2427 .OR,
   opAt 2428 (.Swap ⟨1, by decide⟩),
   opAt 2429 (.Dup ⟨1, by decide⟩),
   opAt 2430 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2431 1 31,
   opAt 2432 .NOT,
   opAt 2433 .ADD,
   pushAt 2434 2 2111,
   opAt 2435 (.Dup ⟨1, by decide⟩),
   opAt 2436 .GT,
   pushAt 2437 2 3081,
   opAt 2438 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
