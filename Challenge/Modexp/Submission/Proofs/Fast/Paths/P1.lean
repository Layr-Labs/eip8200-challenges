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
  [pushAt 897 1 32,
   opAt 898 (.Dup ⟨6, by decide⟩),
   opAt 899 (.Dup ⟨2, by decide⟩),
   opAt 900 .ADD,
   opAt 901 .SUB,
   opAt 902 .CALLDATALOAD,
   pushAt 903 1 1,
   opAt 904 .AND,
   opAt 905 .ISZERO,
   pushAt 906 2 1599,
   opAt 907 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
