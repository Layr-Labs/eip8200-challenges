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
  [pushAt 1023 1 32,
   opAt 1024 (.Dup ⟨6, by decide⟩),
   opAt 1025 (.Dup ⟨2, by decide⟩),
   opAt 1026 .ADD,
   opAt 1027 .SUB,
   opAt 1028 .CALLDATALOAD,
   pushAt 1029 1 1,
   opAt 1030 .AND,
   opAt 1031 .ISZERO,
   pushAt 1032 2 1876,
   opAt 1033 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
