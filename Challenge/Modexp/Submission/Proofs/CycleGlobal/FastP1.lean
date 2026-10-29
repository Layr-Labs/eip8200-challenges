import Challenge.Modexp.Submission.Proofs.CycleGlobal.PredicateIdentity
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 1 (instructions 1163..1120). -/

namespace CycleSubmission.Global.Fast
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 461..481, pc 650..675: the rewritten entry check. -/
def blk1028 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 437 1 32,
   opAt 438 (.Dup ⟨6, by decide⟩),
   opAt 439 (.Dup ⟨2, by decide⟩),
   opAt 440 .ADD,
   opAt 441 .SUB,
   opAt 442 .CALLDATALOAD,
   opAt 443 .NOT,
   opAt 444 (.Dup ⟨0, by decide⟩),
   opAt 445 .ISZERO,
   opAt 446 (.Swap ⟨0, by decide⟩),
   pushAt 447 2 1,
   opAt 448 .AND,
   opAt 449 .OR,
   opAt 450 (.Dup ⟨6, by decide⟩),
   pushAt 451 2 127,
   opAt 452 .AND,
   opAt 453 .OR,
   pushAt 454 1 219,
   opAt 455 .JUMPI]

end CycleSubmission.Global.Fast
