import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 1 (instructions 1028..1038). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1028..1038, pc 1385..1399. -/
def blk1028 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3850 1 32,
   opAt 3851 (.Dup ⟨6, by decide⟩),
   opAt 3852 (.Dup ⟨2, by decide⟩),
   opAt 3853 .ADD,
   opAt 3854 .SUB,
   opAt 3855 .CALLDATALOAD,
   pushAt 3856 1 1,
   opAt 3857 .AND,
   opAt 3858 .ISZERO,
   pushAt 3859 2 1454,
   opAt 3860 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
