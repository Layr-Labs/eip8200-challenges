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
  [pushAt 971 1 32,
   opAt 972 (.Dup ⟨6, by decide⟩),
   opAt 973 (.Dup ⟨2, by decide⟩),
   opAt 974 .ADD,
   opAt 975 .SUB,
   opAt 976 .CALLDATALOAD,
   pushAt 977 1 1,
   opAt 978 .AND,
   opAt 979 .ISZERO,
   pushAt 980 2 1714,
   opAt 981 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
