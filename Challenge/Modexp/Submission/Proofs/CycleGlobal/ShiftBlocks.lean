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
  [opAt 2353 .JUMPDEST,
   opAt 2354 (.Dup dA0),
   opAt 2355 .MLOAD,
   pushAt 2356 2 2112,
   opAt 2357 (.Dup dA2),
   opAt 2358 .SUB,
   opAt 2359 .MLOAD,
   opAt 2360 (.Dup dA1),
   opAt 2361 .ADD,
   opAt 2362 (.Swap sA0),
   opAt 2363 (.Dup dA1),
   opAt 2364 .LT,
   opAt 2365 (.Swap sA0),
   opAt 2366 (.Dup dA3),
   opAt 2367 .ADD,
   opAt 2368 (.Swap sA2),
   opAt 2369 (.Dup dA3),
   opAt 2370 .LT,
   opAt 2371 .OR,
   opAt 2372 (.Swap sA1),
   opAt 2373 (.Dup dA1),
   opAt 2374 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2375 1 31,
   opAt 2376 .NOT,
   opAt 2377 .ADD,
   pushAt 2378 2 2111,
   opAt 2379 (.Dup dA1),
   opAt 2380 .GT,
   pushAt 2381 2 3077,
   opAt 2382 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
