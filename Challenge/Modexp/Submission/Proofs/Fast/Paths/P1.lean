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
  [pushAt 534 1 32,
   opAt 535 (.Dup ⟨6, by decide⟩),
   opAt 536 (.Dup ⟨2, by decide⟩),
   opAt 537 .ADD,
   opAt 538 .SUB,
   opAt 539 .CALLDATALOAD,
   pushAt 540 1 1,
   opAt 541 .AND,
   opAt 542 .ISZERO,
   pushAt 543 2 1176,
   opAt 544 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
