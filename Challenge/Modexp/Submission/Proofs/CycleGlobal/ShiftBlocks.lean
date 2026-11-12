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
  [opAt 2395 .JUMPDEST,
   opAt 2396 (.Dup dA0),
   opAt 2397 .MLOAD,
   pushAt 2398 2 2112,
   opAt 2399 (.Dup dA2),
   opAt 2400 .SUB,
   opAt 2401 .MLOAD,
   opAt 2402 (.Dup dA1),
   opAt 2403 .ADD,
   opAt 2404 (.Swap sA0),
   opAt 2405 (.Dup dA1),
   opAt 2406 .LT,
   opAt 2407 (.Swap sA0),
   opAt 2408 (.Dup dA3),
   opAt 2409 .ADD,
   opAt 2410 (.Swap sA2),
   opAt 2411 (.Dup dA3),
   opAt 2412 .LT,
   opAt 2413 .OR,
   opAt 2414 (.Swap sA1),
   opAt 2415 (.Dup dA1),
   opAt 2416 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2417 1 31,
   opAt 2418 .NOT,
   opAt 2419 .ADD,
   pushAt 2420 2 2111,
   opAt 2421 (.Dup dA1),
   opAt 2422 .GT,
   pushAt 2423 2 3087,
   opAt 2424 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
