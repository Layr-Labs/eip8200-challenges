import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1451..1550). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1451..1505, pc 2053..2062. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 735 .JUMPDEST,
   pushAt 736 1 1,
   opAt 737 (.Swap ⟨0, by decide⟩),
   opAt 738 .SUB,
   opAt 739 (.Dup ⟨0, by decide⟩),
   pushAt 740 2 1073,
   opAt 741 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2065. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 742 .POP,
   opAt 743 .POP,
   opAt 744 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
