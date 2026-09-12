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
  [pushAt 972 1 32,
   opAt 973 (.Dup ⟨6, by decide⟩),
   opAt 974 (.Dup ⟨2, by decide⟩),
   opAt 975 .ADD,
   opAt 976 .SUB,
   opAt 977 .CALLDATALOAD,
   pushAt 978 1 1,
   opAt 979 .AND,
   opAt 980 .ISZERO,
   pushAt 981 2 1717,
   opAt 982 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
