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
  [opAt 2396 .JUMPDEST,
   opAt 2397 (.Dup ⟨0, by decide⟩),
   opAt 2398 .MLOAD,
   pushAt 2399 2 2112,
   opAt 2400 (.Dup ⟨2, by decide⟩),
   opAt 2401 .SUB,
   opAt 2402 .MLOAD,
   opAt 2403 (.Dup ⟨1, by decide⟩),
   opAt 2404 .ADD,
   opAt 2405 (.Swap ⟨0, by decide⟩),
   opAt 2406 (.Dup ⟨1, by decide⟩),
   opAt 2407 .LT,
   opAt 2408 (.Swap ⟨0, by decide⟩),
   opAt 2409 (.Dup ⟨3, by decide⟩),
   opAt 2410 .ADD,
   opAt 2411 (.Swap ⟨2, by decide⟩),
   opAt 2412 (.Dup ⟨3, by decide⟩),
   opAt 2413 .LT,
   opAt 2414 .OR,
   opAt 2415 (.Swap ⟨1, by decide⟩),
   opAt 2416 (.Dup ⟨1, by decide⟩),
   opAt 2417 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2418 1 31,
   opAt 2419 .NOT,
   opAt 2420 .ADD,
   pushAt 2421 2 2111,
   opAt 2422 (.Dup ⟨1, by decide⟩),
   opAt 2423 .GT,
   pushAt 2424 2 3112,
   opAt 2425 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
