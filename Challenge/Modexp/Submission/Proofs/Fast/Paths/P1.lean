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
  [pushAt 985 1 32,
   opAt 986 (.Dup ⟨6, by decide⟩),
   opAt 987 (.Dup ⟨2, by decide⟩),
   opAt 988 .ADD,
   opAt 989 .SUB,
   opAt 990 .CALLDATALOAD,
   pushAt 991 1 1,
   opAt 992 .AND,
   opAt 993 .ISZERO,
   pushAt 994 2 1745,
   opAt 995 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
