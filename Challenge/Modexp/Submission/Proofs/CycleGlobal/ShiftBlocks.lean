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
  [opAt 2350 .JUMPDEST,
   opAt 2351 (.Dup dA0),
   opAt 2352 .MLOAD,
   pushAt 2353 2 2112,
   opAt 2354 (.Dup dA2),
   opAt 2355 .SUB,
   opAt 2356 .MLOAD,
   opAt 2357 (.Dup dA1),
   opAt 2358 .ADD,
   opAt 2359 (.Swap sA0),
   opAt 2360 (.Dup dA1),
   opAt 2361 .LT,
   opAt 2362 (.Swap sA0),
   opAt 2363 (.Dup dA3),
   opAt 2364 .ADD,
   opAt 2365 (.Swap sA2),
   opAt 2366 (.Dup dA3),
   opAt 2367 .LT,
   opAt 2368 .OR,
   opAt 2369 (.Swap sA1),
   opAt 2370 (.Dup dA1),
   opAt 2371 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2372 1 31,
   opAt 2373 .NOT,
   opAt 2374 .ADD,
   pushAt 2375 2 2111,
   opAt 2376 (.Dup dA1),
   opAt 2377 .GT,
   pushAt 2378 2 3077,
   opAt 2379 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

end CycleSubmission.Global.Fast
