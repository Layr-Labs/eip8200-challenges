import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 1 (instructions 1163..1120). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1163..1120, pc 1515..1481. -/
def blk1028 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 535 1 32,
   opAt 536 (.Dup ⟨6, by decide⟩),
   opAt 537 (.Dup ⟨2, by decide⟩),
   opAt 538 .ADD,
   opAt 539 .SUB,
   opAt 540 .CALLDATALOAD,
   pushAt 541 1 1,
   opAt 542 .AND,
   opAt 543 .ISZERO,
   pushAt 544 2 1180,
   opAt 545 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
