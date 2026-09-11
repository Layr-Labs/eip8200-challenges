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
  [pushAt 910 1 32,
   opAt 911 (.Dup ⟨6, by decide⟩),
   opAt 912 (.Dup ⟨2, by decide⟩),
   opAt 913 .ADD,
   opAt 914 .SUB,
   opAt 915 .CALLDATALOAD,
   pushAt 916 1 1,
   opAt 917 .AND,
   opAt 918 .ISZERO,
   pushAt 919 2 1628,
   opAt 920 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
