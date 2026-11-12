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
  [opAt 2392 .JUMPDEST,
   opAt 2393 (.Dup ⟨0,by decide⟩),
   opAt 2394 .MLOAD,
   pushAt 2395 2 2112,
   opAt 2396 (.Dup ⟨2,by decide⟩),
   opAt 2397 .SUB,
   opAt 2398 .MLOAD,
   opAt 2399 (.Dup ⟨1,by decide⟩),
   opAt 2400 .ADD,
   opAt 2401 (.Swap ⟨0,by decide⟩),
   opAt 2402 (.Dup ⟨1,by decide⟩),
   opAt 2403 .LT,
   opAt 2404 (.Swap ⟨0,by decide⟩),
   opAt 2405 (.Dup ⟨3,by decide⟩),
   opAt 2406 .ADD,
   opAt 2407 (.Swap ⟨2,by decide⟩),
   opAt 2408 (.Dup ⟨3,by decide⟩),
   opAt 2409 .LT,
   opAt 2410 .OR,
   opAt 2411 (.Swap ⟨1,by decide⟩),
   opAt 2412 (.Dup ⟨1,by decide⟩),
   opAt 2413 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2414 1 31,
   opAt 2415 .NOT,
   opAt 2416 .ADD,
   pushAt 2417 2 2111,
   opAt 2418 (.Dup ⟨1,by decide⟩),
   opAt 2419 .GT,
   pushAt 2420 2 3087,
   opAt 2421 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
