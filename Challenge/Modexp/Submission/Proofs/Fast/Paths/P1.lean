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
   opAt 464 .NOT,
   opAt 465 .ISZERO,
   opAt 466 (.Swap ⟨0, by decide⟩),
   pushAt 467 2 1,
   opAt 468 .AND,
   opAt 469 .ISZERO,
   opAt 470 .OR,
   opAt 471 (.Dup ⟨6, by decide⟩),
   pushAt 472 1 127,
   opAt 473 .AND,
   opAt 474 .OR,
   pushAt 475 2 800,
   opAt 476 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
