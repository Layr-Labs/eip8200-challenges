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
  [opAt 2405 .JUMPDEST,
   opAt 2406 (.Dup ⟨0, by decide⟩),
   opAt 2407 .MLOAD,
   pushAt 2408 2 2112,
   opAt 2409 (.Dup ⟨2, by decide⟩),
   opAt 2410 .SUB,
   opAt 2411 .MLOAD,
   opAt 2412 (.Dup ⟨1, by decide⟩),
   opAt 2413 .ADD,
   opAt 2414 (.Swap ⟨0, by decide⟩),
   opAt 2415 (.Dup ⟨1, by decide⟩),
   opAt 2416 .LT,
   opAt 2417 (.Swap ⟨0, by decide⟩),
   opAt 2418 (.Dup ⟨3, by decide⟩),
   opAt 2419 .ADD,
   opAt 2420 (.Swap ⟨2, by decide⟩),
   opAt 2421 (.Dup ⟨3, by decide⟩),
   opAt 2422 .LT,
   opAt 2423 .OR,
   opAt 2424 (.Swap ⟨1, by decide⟩),
   opAt 2425 (.Dup ⟨1, by decide⟩),
   opAt 2426 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2427 1 31,
   opAt 2428 .NOT,
   opAt 2429 .ADD,
   pushAt 2430 2 2111,
   opAt 2431 (.Dup ⟨1, by decide⟩),
   opAt 2432 .GT,
   pushAt 2433 2 3112,
   opAt 2434 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
