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
  [pushAt 438 1 32,
   opAt 439 (.Dup ⟨6, by decide⟩),
   opAt 440 (.Dup ⟨2, by decide⟩),
   opAt 441 .ADD,
   opAt 442 .SUB,
   opAt 443 .CALLDATALOAD,
   opAt 444 .NOT,
   opAt 445 (.Dup ⟨0, by decide⟩),
   opAt 446 .ISZERO,
   opAt 447 (.Swap ⟨0, by decide⟩),
   pushAt 448 2 1,
   opAt 449 .AND,
   opAt 450 .OR,
   opAt 451 (.Dup ⟨6, by decide⟩),
   pushAt 452 2 127,
   opAt 453 .AND,
   opAt 454 .OR,
   pushAt 455 1 219,
   opAt 456 .JUMPI]

end CycleSubmission.Global.Fast
