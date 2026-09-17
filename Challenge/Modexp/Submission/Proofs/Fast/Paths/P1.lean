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
  [pushAt 461 1 32,
   opAt 462 (.Dup ⟨6, by decide⟩),
   opAt 463 (.Dup ⟨2, by decide⟩),
   opAt 464 .ADD,
   opAt 465 .SUB,
   opAt 466 .CALLDATALOAD,
   pushAt 467 1 1,
   opAt 468 .AND,
   opAt 469 .ISZERO,
   pushAt 470 2 1054,
   opAt 471 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
