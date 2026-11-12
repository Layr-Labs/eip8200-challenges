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
  [opAt 2390 .JUMPDEST,
   opAt 2391 (.Dup ⟨0,by decide⟩),
   opAt 2392 .MLOAD,
   pushAt 2393 2 2112,
   opAt 2394 (.Dup ⟨2,by decide⟩),
   opAt 2395 .SUB,
   opAt 2396 .MLOAD,
   opAt 2397 (.Dup ⟨1,by decide⟩),
   opAt 2398 .ADD,
   opAt 2399 (.Swap ⟨0,by decide⟩),
   opAt 2400 (.Dup ⟨1,by decide⟩),
   opAt 2401 .LT,
   opAt 2402 (.Swap ⟨0,by decide⟩),
   opAt 2403 (.Dup ⟨3,by decide⟩),
   opAt 2404 .ADD,
   opAt 2405 (.Swap ⟨2,by decide⟩),
   opAt 2406 (.Dup ⟨3,by decide⟩),
   opAt 2407 .LT,
   opAt 2408 .OR,
   opAt 2409 (.Swap ⟨1,by decide⟩),
   opAt 2410 (.Dup ⟨1,by decide⟩),
   opAt 2411 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2412 1 31,
   opAt 2413 .NOT,
   opAt 2414 .ADD,
   pushAt 2415 2 2111,
   opAt 2416 (.Dup ⟨1,by decide⟩),
   opAt 2417 .GT,
   pushAt 2418 2 3083,
   opAt 2419 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
