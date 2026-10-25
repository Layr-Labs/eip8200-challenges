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
  [opAt 2407 .JUMPDEST,
   opAt 2408 (.Dup ⟨0, by decide⟩),
   opAt 2409 .MLOAD,
   pushAt 2410 2 2112,
   opAt 2411 (.Dup ⟨2, by decide⟩),
   opAt 2412 .SUB,
   opAt 2413 .MLOAD,
   opAt 2414 (.Dup ⟨1, by decide⟩),
   opAt 2415 .ADD,
   opAt 2416 (.Swap ⟨0, by decide⟩),
   opAt 2417 (.Dup ⟨1, by decide⟩),
   opAt 2418 .LT,
   opAt 2419 (.Swap ⟨0, by decide⟩),
   opAt 2420 (.Dup ⟨3, by decide⟩),
   opAt 2421 .ADD,
   opAt 2422 (.Swap ⟨2, by decide⟩),
   opAt 2423 (.Dup ⟨3, by decide⟩),
   opAt 2424 .LT,
   opAt 2425 .OR,
   opAt 2426 (.Swap ⟨1, by decide⟩),
   opAt 2427 (.Dup ⟨1, by decide⟩),
   opAt 2428 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2429 1 31,
   opAt 2430 .NOT,
   opAt 2431 .ADD,
   pushAt 2432 2 2111,
   opAt 2433 (.Dup ⟨1, by decide⟩),
   opAt 2434 .GT,
   pushAt 2435 2 3081,
   opAt 2436 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
