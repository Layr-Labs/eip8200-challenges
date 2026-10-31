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
  [opAt 2415 .JUMPDEST,
   opAt 2416 (.Dup ⟨0, by decide⟩),
   opAt 2417 .MLOAD,
   pushAt 2418 2 2112,
   opAt 2419 (.Dup ⟨2, by decide⟩),
   opAt 2420 .SUB,
   opAt 2421 .MLOAD,
   opAt 2422 (.Dup ⟨1, by decide⟩),
   opAt 2423 .ADD,
   opAt 2424 (.Swap ⟨0, by decide⟩),
   opAt 2425 (.Dup ⟨1, by decide⟩),
   opAt 2426 .LT,
   opAt 2427 (.Swap ⟨0, by decide⟩),
   opAt 2428 (.Dup ⟨3, by decide⟩),
   opAt 2429 .ADD,
   opAt 2430 (.Swap ⟨2, by decide⟩),
   opAt 2431 (.Dup ⟨3, by decide⟩),
   opAt 2432 .LT,
   opAt 2433 .OR,
   opAt 2434 (.Swap ⟨1, by decide⟩),
   opAt 2435 (.Dup ⟨1, by decide⟩),
   opAt 2436 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2437 1 31,
   opAt 2438 .NOT,
   opAt 2439 .ADD,
   pushAt 2440 2 2111,
   opAt 2441 (.Dup ⟨1, by decide⟩),
   opAt 2442 .GT,
   pushAt 2443 2 3112,
   opAt 2444 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
