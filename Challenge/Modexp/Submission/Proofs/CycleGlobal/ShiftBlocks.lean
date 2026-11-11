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
  [opAt 2380 .JUMPDEST,
   opAt 2381 (.Dup dA0),
   opAt 2382 .MLOAD,
   pushAt 2383 2 2112,
   opAt 2384 (.Dup dA2),
   opAt 2385 .SUB,
   opAt 2386 .MLOAD,
   opAt 2387 (.Dup dA1),
   opAt 2388 .ADD,
   opAt 2389 (.Swap sA0),
   opAt 2390 (.Dup dA1),
   opAt 2391 .LT,
   opAt 2392 (.Swap sA0),
   opAt 2393 (.Dup dA3),
   opAt 2394 .ADD,
   opAt 2395 (.Swap sA2),
   opAt 2396 (.Dup dA3),
   opAt 2397 .LT,
   opAt 2398 .OR,
   opAt 2399 (.Swap sA1),
   opAt 2400 (.Dup dA1),
   opAt 2401 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2402 1 31,
   opAt 2403 .NOT,
   opAt 2404 .ADD,
   pushAt 2405 2 2111,
   opAt 2406 (.Dup dA1),
   opAt 2407 .GT,
   pushAt 2408 2 3077,
   opAt 2409 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
