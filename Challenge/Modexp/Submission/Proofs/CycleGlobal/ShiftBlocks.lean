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
  [opAt 2372 .JUMPDEST,
   opAt 2373 (.Dup ⟨0,by decide⟩),
   opAt 2374 .MLOAD,
   pushAt 2375 2 2112,
   opAt 2376 (.Dup ⟨2,by decide⟩),
   opAt 2377 .SUB,
   opAt 2378 .MLOAD,
   opAt 2379 (.Dup ⟨1,by decide⟩),
   opAt 2380 .ADD,
   opAt 2381 (.Swap ⟨0,by decide⟩),
   opAt 2382 (.Dup ⟨1,by decide⟩),
   opAt 2383 .LT,
   opAt 2384 (.Swap ⟨0,by decide⟩),
   opAt 2385 (.Dup ⟨3,by decide⟩),
   opAt 2386 .ADD,
   opAt 2387 (.Swap ⟨2,by decide⟩),
   opAt 2388 (.Dup ⟨3,by decide⟩),
   opAt 2389 .LT,
   opAt 2390 .OR,
   opAt 2391 (.Swap ⟨1,by decide⟩),
   opAt 2392 (.Dup ⟨1,by decide⟩),
   opAt 2393 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2394 1 31,
   opAt 2395 .NOT,
   opAt 2396 .ADD,
   pushAt 2397 2 2111,
   opAt 2398 (.Dup ⟨1,by decide⟩),
   opAt 2399 .GT,
   pushAt 2400 2 3067,
   opAt 2401 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
