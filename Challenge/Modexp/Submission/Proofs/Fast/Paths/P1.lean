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
  [pushAt 440 1 32,
   opAt 441 (.Dup ⟨6, by decide⟩),
   opAt 442 (.Dup ⟨2, by decide⟩),
   opAt 443 .ADD,
   opAt 444 .SUB,
   opAt 445 .CALLDATALOAD,
   opAt 446 (.Dup ⟨0, by decide⟩),
   pushAt 447 0 0,
   opAt 448 .NOT,
   opAt 449 .EQ,
   opAt 450 (.Swap ⟨0, by decide⟩),
   pushAt 451 1 1,
   opAt 452 .AND,
   opAt 453 .ISZERO,
   opAt 454 .OR,
   opAt 455 (.Dup ⟨6, by decide⟩),
   pushAt 456 1 127,
   opAt 457 .AND,
   opAt 458 .OR,
   pushAt 459 2 761,
   opAt 460 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
