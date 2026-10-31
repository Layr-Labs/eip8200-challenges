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
  [opAt 2416 .JUMPDEST,
   opAt 2417 (.Dup ⟨0, by decide⟩),
   opAt 2418 .MLOAD,
   pushAt 2419 2 2112,
   opAt 2420 (.Dup ⟨2, by decide⟩),
   opAt 2421 .SUB,
   opAt 2422 .MLOAD,
   opAt 2423 (.Dup ⟨1, by decide⟩),
   opAt 2424 .ADD,
   opAt 2425 (.Swap ⟨0, by decide⟩),
   opAt 2426 (.Dup ⟨1, by decide⟩),
   opAt 2427 .LT,
   opAt 2428 (.Swap ⟨0, by decide⟩),
   opAt 2429 (.Dup ⟨3, by decide⟩),
   opAt 2430 .ADD,
   opAt 2431 (.Swap ⟨2, by decide⟩),
   opAt 2432 (.Dup ⟨3, by decide⟩),
   opAt 2433 .LT,
   opAt 2434 .OR,
   opAt 2435 (.Swap ⟨1, by decide⟩),
   opAt 2436 (.Dup ⟨1, by decide⟩),
   opAt 2437 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2438 1 31,
   opAt 2439 .NOT,
   opAt 2440 .ADD,
   pushAt 2441 2 2111,
   opAt 2442 (.Dup ⟨1, by decide⟩),
   opAt 2443 .GT,
   pushAt 2444 2 3112,
   opAt 2445 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
