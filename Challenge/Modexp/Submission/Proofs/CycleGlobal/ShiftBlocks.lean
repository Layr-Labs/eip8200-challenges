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
  [opAt 2382 .JUMPDEST,
   opAt 2383 (.Dup dA0),
   opAt 2384 .MLOAD,
   pushAt 2385 2 2112,
   opAt 2386 (.Dup dA2),
   opAt 2387 .SUB,
   opAt 2388 .MLOAD,
   opAt 2389 (.Dup dA1),
   opAt 2390 .ADD,
   opAt 2391 (.Swap sA0),
   opAt 2392 (.Dup dA1),
   opAt 2393 .LT,
   opAt 2394 (.Swap sA0),
   opAt 2395 (.Dup dA3),
   opAt 2396 .ADD,
   opAt 2397 (.Swap sA2),
   opAt 2398 (.Dup dA3),
   opAt 2399 .LT,
   opAt 2400 .OR,
   opAt 2401 (.Swap sA1),
   opAt 2402 (.Dup dA1),
   opAt 2403 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2404 1 31,
   opAt 2405 .NOT,
   opAt 2406 .ADD,
   pushAt 2407 2 2111,
   opAt 2408 (.Dup dA1),
   opAt 2409 .GT,
   pushAt 2410 2 3077,
   opAt 2411 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
