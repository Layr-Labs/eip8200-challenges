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
  [opAt 2375 .JUMPDEST,
   opAt 2376 (.Dup ⟨0,by decide⟩),
   opAt 2377 .MLOAD,
   pushAt 2378 2 2112,
   opAt 2379 (.Dup ⟨2,by decide⟩),
   opAt 2380 .SUB,
   opAt 2381 .MLOAD,
   opAt 2382 (.Dup ⟨1,by decide⟩),
   opAt 2383 .ADD,
   opAt 2384 (.Swap ⟨0,by decide⟩),
   opAt 2385 (.Dup ⟨1,by decide⟩),
   opAt 2386 .LT,
   opAt 2387 (.Swap ⟨0,by decide⟩),
   opAt 2388 (.Dup ⟨3,by decide⟩),
   opAt 2389 .ADD,
   opAt 2390 (.Swap ⟨2,by decide⟩),
   opAt 2391 (.Dup ⟨3,by decide⟩),
   opAt 2392 .LT,
   opAt 2393 .OR,
   opAt 2394 (.Swap ⟨1,by decide⟩),
   opAt 2395 (.Dup ⟨1,by decide⟩),
   opAt 2396 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2397 1 31,
   opAt 2398 .NOT,
   opAt 2399 .ADD,
   pushAt 2400 2 2111,
   opAt 2401 (.Dup ⟨1,by decide⟩),
   opAt 2402 .GT,
   pushAt 2403 2 3067,
   opAt 2404 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
