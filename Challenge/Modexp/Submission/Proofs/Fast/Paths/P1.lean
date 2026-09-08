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
  [pushAt 1022 1 32,
   opAt 1023 (.Dup ⟨6, by decide⟩),
   opAt 1024 (.Dup ⟨2, by decide⟩),
   opAt 1025 .ADD,
   opAt 1026 .SUB,
   opAt 1027 .CALLDATALOAD,
   pushAt 1028 1 1,
   opAt 1029 .AND,
   opAt 1030 .ISZERO,
   pushAt 1031 2 1869,
   opAt 1032 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
