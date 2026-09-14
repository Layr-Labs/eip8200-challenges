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
  [pushAt 532 1 32,
   opAt 533 (.Dup ⟨6, by decide⟩),
   opAt 534 (.Dup ⟨2, by decide⟩),
   opAt 535 .ADD,
   opAt 536 .SUB,
   opAt 537 .CALLDATALOAD,
   pushAt 538 1 1,
   opAt 539 .AND,
   opAt 540 .ISZERO,
   pushAt 541 2 1164,
   opAt 542 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
