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
  [pushAt 1021 1 32,
   opAt 1022 (.Dup ⟨6, by decide⟩),
   opAt 1023 (.Dup ⟨2, by decide⟩),
   opAt 1024 .ADD,
   opAt 1025 .SUB,
   opAt 1026 .CALLDATALOAD,
   pushAt 1027 1 1,
   opAt 1028 .AND,
   opAt 1029 .ISZERO,
   pushAt 1030 2 1881,
   opAt 1031 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
