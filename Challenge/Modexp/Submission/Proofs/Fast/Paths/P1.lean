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
  [pushAt 459 1 32,
   opAt 460 (.Dup ⟨6, by decide⟩),
   opAt 461 (.Dup ⟨2, by decide⟩),
   opAt 462 .ADD,
   opAt 463 .SUB,
   opAt 464 .CALLDATALOAD,
   pushAt 465 1 1,
   opAt 466 .AND,
   opAt 467 .ISZERO,
   pushAt 468 2 1053,
   opAt 469 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
