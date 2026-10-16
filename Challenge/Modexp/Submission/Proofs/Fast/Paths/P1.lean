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
  [pushAt 438 1 32,
   opAt 439 (.Dup ⟨6, by decide⟩),
   opAt 440 (.Dup ⟨2, by decide⟩),
   opAt 441 .ADD,
   opAt 442 .SUB,
   opAt 443 .CALLDATALOAD,
   opAt 444 (.Dup ⟨0, by decide⟩),
   pushAt 445 0 0,
   opAt 446 .NOT,
   opAt 447 .EQ,
   opAt 448 (.Swap ⟨0, by decide⟩),
   pushAt 449 1 1,
   opAt 450 .AND,
   opAt 451 .ISZERO,
   opAt 452 .OR,
   opAt 453 (.Dup ⟨6, by decide⟩),
   pushAt 454 1 127,
   opAt 455 .AND,
   opAt 456 .OR,
   pushAt 457 1 219,
   opAt 458 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
