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
  [pushAt 975 1 32,
   opAt 976 (.Dup ⟨6, by decide⟩),
   opAt 977 (.Dup ⟨2, by decide⟩),
   opAt 978 .ADD,
   opAt 979 .SUB,
   opAt 980 .CALLDATALOAD,
   pushAt 981 1 1,
   opAt 982 .AND,
   opAt 983 .ISZERO,
   pushAt 984 2 1722,
   opAt 985 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
