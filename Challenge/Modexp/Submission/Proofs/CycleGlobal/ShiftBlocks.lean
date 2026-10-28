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
  [opAt 2397 .JUMPDEST,
   opAt 2398 (.Dup ⟨0, by decide⟩),
   opAt 2399 .MLOAD,
   pushAt 2400 2 2112,
   opAt 2401 (.Dup ⟨2, by decide⟩),
   opAt 2402 .SUB,
   opAt 2403 .MLOAD,
   opAt 2404 (.Dup ⟨1, by decide⟩),
   opAt 2405 .ADD,
   opAt 2406 (.Swap ⟨0, by decide⟩),
   opAt 2407 (.Dup ⟨1, by decide⟩),
   opAt 2408 .LT,
   opAt 2409 (.Swap ⟨0, by decide⟩),
   opAt 2410 (.Dup ⟨3, by decide⟩),
   opAt 2411 .ADD,
   opAt 2412 (.Swap ⟨2, by decide⟩),
   opAt 2413 (.Dup ⟨3, by decide⟩),
   opAt 2414 .LT,
   opAt 2415 .OR,
   opAt 2416 (.Swap ⟨1, by decide⟩),
   opAt 2417 (.Dup ⟨1, by decide⟩),
   opAt 2418 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2419 1 31,
   opAt 2420 .NOT,
   opAt 2421 .ADD,
   pushAt 2422 2 2111,
   opAt 2423 (.Dup ⟨1, by decide⟩),
   opAt 2424 .GT,
   pushAt 2425 2 3081,
   opAt 2426 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
