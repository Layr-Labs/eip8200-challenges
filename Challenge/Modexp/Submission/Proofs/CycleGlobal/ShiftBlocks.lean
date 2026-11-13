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
  [opAt 2362 .JUMPDEST,
   opAt 2363 (.Dup ⟨0,by decide⟩),
   opAt 2364 .MLOAD,
   pushAt 2365 2 2112,
   opAt 2366 (.Dup ⟨2,by decide⟩),
   opAt 2367 .SUB,
   opAt 2368 .MLOAD,
   opAt 2369 (.Dup ⟨1,by decide⟩),
   opAt 2370 .ADD,
   opAt 2371 (.Swap ⟨0,by decide⟩),
   opAt 2372 (.Dup ⟨1,by decide⟩),
   opAt 2373 .LT,
   opAt 2374 (.Swap ⟨0,by decide⟩),
   opAt 2375 (.Dup ⟨3,by decide⟩),
   opAt 2376 .ADD,
   opAt 2377 (.Swap ⟨2,by decide⟩),
   opAt 2378 (.Dup ⟨3,by decide⟩),
   opAt 2379 .LT,
   opAt 2380 .OR,
   opAt 2381 (.Swap ⟨1,by decide⟩),
   opAt 2382 (.Dup ⟨1,by decide⟩),
   opAt 2383 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2384 1 31,
   opAt 2385 .NOT,
   opAt 2386 .ADD,
   pushAt 2387 2 2111,
   opAt 2388 (.Dup ⟨1,by decide⟩),
   opAt 2389 .GT,
   pushAt 2390 2 3014,
   opAt 2391 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
