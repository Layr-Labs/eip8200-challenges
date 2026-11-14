import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Fast.ShiftPaths
open CycleSubmission.SharedStackArgs
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Loop-body blocks of the shift-reduce routine split before their exit tests, so
that each block reduction stays small enough for the kernel. -/
namespace Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2409 .JUMPDEST,
   opAt 2410 (.Dup dA0),
   opAt 2411 .MLOAD,
   pushAt 2412 2 2112,
   opAt 2413 (.Dup dA2),
   opAt 2414 .SUB,
   opAt 2415 .MLOAD,
   opAt 2416 (.Dup dA1),
   opAt 2417 .ADD,
   opAt 2418 (.Swap sA0),
   opAt 2419 (.Dup dA1),
   opAt 2420 .LT,
   opAt 2421 (.Swap sA0),
   opAt 2422 (.Dup dA3),
   opAt 2423 .ADD,
   opAt 2424 (.Swap sA2),
   opAt 2425 (.Dup dA3),
   opAt 2426 .LT,
   opAt 2427 .OR,
   opAt 2428 (.Swap sA1),
   opAt 2429 (.Dup dA1),
   opAt 2430 .MSTORE]
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2431 1 31,
   opAt 2432 .NOT,
   opAt 2433 .ADD,
   pushAt 2434 2 2111,
   opAt 2435 (.Dup dA1),
   opAt 2436 .GT,
   pushAt 2437 2 3081,
   opAt 2438 .JUMPI]
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []
end Challenge.Modexp.Submission.Proofs.Fast
