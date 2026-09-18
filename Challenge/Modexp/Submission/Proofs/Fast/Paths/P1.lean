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
  [pushAt 457 1 32,
   opAt 458 (.Dup ⟨6, by decide⟩),
   opAt 459 (.Dup ⟨2, by decide⟩),
   opAt 460 .ADD,
   opAt 461 .SUB,
   opAt 462 .CALLDATALOAD,
   opAt 463 (.Dup ⟨0, by decide⟩),
   pushAt 464 0 0,
   opAt 465 .NOT,
   opAt 466 .EQ,
   opAt 467 (.Swap ⟨0, by decide⟩),
   pushAt 468 1 1,
   opAt 469 .AND,
   opAt 470 .ISZERO,
   opAt 471 .OR,
   opAt 472 (.Dup ⟨6, by decide⟩),
   pushAt 473 1 127,
   opAt 474 .AND,
   opAt 475 .OR,
   pushAt 476 2 790,
   opAt 477 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
