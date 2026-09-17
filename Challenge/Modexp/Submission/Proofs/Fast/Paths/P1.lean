import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 1 (instructions 1163..1120). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 461..481, pc 650..675: the rewritten entry check. -/
def blk1028 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 461 1 32,
   opAt 462 (.Dup ⟨6, by decide⟩),
   opAt 463 (.Dup ⟨2, by decide⟩),
   opAt 464 .ADD,
   opAt 465 .SUB,
   opAt 466 .CALLDATALOAD,
   opAt 467 (.Dup ⟨0, by decide⟩),
   pushAt 468 0 0,
   opAt 469 .NOT,
   opAt 470 .EQ,
   opAt 471 (.Swap ⟨0, by decide⟩),
   pushAt 472 1 1,
   opAt 473 .AND,
   opAt 474 .ISZERO,
   opAt 475 .OR,
   opAt 476 (.Dup ⟨6, by decide⟩),
   pushAt 477 1 127,
   opAt 478 .AND,
   opAt 479 .OR,
   pushAt 480 2 1065,
   opAt 481 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
