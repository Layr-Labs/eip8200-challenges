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
  [opAt 2373 .JUMPDEST,
   opAt 2374 (.Dup ⟨0,by decide⟩),
   opAt 2375 .MLOAD,
   pushAt 2376 2 2112,
   opAt 2377 (.Dup ⟨2,by decide⟩),
   opAt 2378 .SUB,
   opAt 2379 .MLOAD,
   opAt 2380 (.Dup ⟨1,by decide⟩),
   opAt 2381 .ADD,
   opAt 2382 (.Swap ⟨0,by decide⟩),
   opAt 2383 (.Dup ⟨1,by decide⟩),
   opAt 2384 .LT,
   opAt 2385 (.Swap ⟨0,by decide⟩),
   opAt 2386 (.Dup ⟨3,by decide⟩),
   opAt 2387 .ADD,
   opAt 2388 (.Swap ⟨2,by decide⟩),
   opAt 2389 (.Dup ⟨3,by decide⟩),
   opAt 2390 .LT,
   opAt 2391 .OR,
   opAt 2392 (.Swap ⟨1,by decide⟩),
   opAt 2393 (.Dup ⟨1,by decide⟩),
   opAt 2394 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2395 1 31,
   opAt 2396 .NOT,
   opAt 2397 .ADD,
   pushAt 2398 2 2111,
   opAt 2399 (.Dup ⟨1,by decide⟩),
   opAt 2400 .GT,
   pushAt 2401 2 3067,
   opAt 2402 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
