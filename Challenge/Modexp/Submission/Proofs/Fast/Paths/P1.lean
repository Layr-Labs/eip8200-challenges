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
  [pushAt 895 1 32,
   opAt 896 (.Dup ⟨6, by decide⟩),
   opAt 897 (.Dup ⟨2, by decide⟩),
   opAt 898 .ADD,
   opAt 899 .SUB,
   opAt 900 .CALLDATALOAD,
   pushAt 901 1 1,
   opAt 902 .AND,
   opAt 903 .ISZERO,
   pushAt 904 2 1583,
   opAt 905 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
