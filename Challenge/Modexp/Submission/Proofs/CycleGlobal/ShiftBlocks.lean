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
  [opAt 2366 .JUMPDEST,
   opAt 2367 (.Dup ⟨0,by decide⟩),
   opAt 2368 .MLOAD,
   pushAt 2369 2 2112,
   opAt 2370 (.Dup ⟨2,by decide⟩),
   opAt 2371 .SUB,
   opAt 2372 .MLOAD,
   opAt 2373 (.Dup ⟨1,by decide⟩),
   opAt 2374 .ADD,
   opAt 2375 (.Swap ⟨0,by decide⟩),
   opAt 2376 (.Dup ⟨1,by decide⟩),
   opAt 2377 .LT,
   opAt 2378 (.Swap ⟨0,by decide⟩),
   opAt 2379 (.Dup ⟨3,by decide⟩),
   opAt 2380 .ADD,
   opAt 2381 (.Swap ⟨2,by decide⟩),
   opAt 2382 (.Dup ⟨3,by decide⟩),
   opAt 2383 .LT,
   opAt 2384 .OR,
   opAt 2385 (.Swap ⟨1,by decide⟩),
   opAt 2386 (.Dup ⟨1,by decide⟩),
   opAt 2387 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2388 1 31,
   opAt 2389 .NOT,
   opAt 2390 .ADD,
   pushAt 2391 2 2111,
   opAt 2392 (.Dup ⟨1,by decide⟩),
   opAt 2393 .GT,
   pushAt 2394 2 3067,
   opAt 2395 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
