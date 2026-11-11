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
  [opAt 2354 .JUMPDEST,
   opAt 2355 (.Dup dA0),
   opAt 2356 .MLOAD,
   pushAt 2357 2 2112,
   opAt 2358 (.Dup dA2),
   opAt 2359 .SUB,
   opAt 2360 .MLOAD,
   opAt 2361 (.Dup dA1),
   opAt 2362 .ADD,
   opAt 2363 (.Swap sA0),
   opAt 2364 (.Dup dA1),
   opAt 2365 .LT,
   opAt 2366 (.Swap sA0),
   opAt 2367 (.Dup dA3),
   opAt 2368 .ADD,
   opAt 2369 (.Swap sA2),
   opAt 2370 (.Dup dA3),
   opAt 2371 .LT,
   opAt 2372 .OR,
   opAt 2373 (.Swap sA1),
   opAt 2374 (.Dup dA1),
   opAt 2375 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2376 1 31,
   opAt 2377 .NOT,
   opAt 2378 .ADD,
   pushAt 2379 2 2111,
   opAt 2380 (.Dup dA1),
   opAt 2381 .GT,
   pushAt 2382 2 3077,
   opAt 2383 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
