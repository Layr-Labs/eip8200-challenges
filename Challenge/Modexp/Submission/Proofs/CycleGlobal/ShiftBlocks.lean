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
  [opAt 2370 .JUMPDEST,
   opAt 2371 (.Dup dA0),
   opAt 2372 .MLOAD,
   pushAt 2373 2 2112,
   opAt 2374 (.Dup dA2),
   opAt 2375 .SUB,
   opAt 2376 .MLOAD,
   opAt 2377 (.Dup dA1),
   opAt 2378 .ADD,
   opAt 2379 (.Swap sA0),
   opAt 2380 (.Dup dA1),
   opAt 2381 .LT,
   opAt 2382 (.Swap sA0),
   opAt 2383 (.Dup dA3),
   opAt 2384 .ADD,
   opAt 2385 (.Swap sA2),
   opAt 2386 (.Dup dA3),
   opAt 2387 .LT,
   opAt 2388 .OR,
   opAt 2389 (.Swap sA1),
   opAt 2390 (.Dup dA1),
   opAt 2391 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2392 1 31,
   opAt 2393 .NOT,
   opAt 2394 .ADD,
   pushAt 2395 2 2111,
   opAt 2396 (.Dup dA1),
   opAt 2397 .GT,
   pushAt 2398 2 3077,
   opAt 2399 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
