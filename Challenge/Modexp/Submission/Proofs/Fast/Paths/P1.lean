import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 1 (instructions 1081..1038). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1081..1038, pc 1433..1399. -/
def blk1028 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 932 1 32,
   opAt 933 (.Dup ⟨6, by decide⟩),
   opAt 934 (.Dup ⟨2, by decide⟩),
   opAt 935 .ADD,
   opAt 936 .SUB,
   opAt 937 .CALLDATALOAD,
   pushAt 938 1 1,
   opAt 939 .AND,
   opAt 940 .ISZERO,
   pushAt 941 2 1635,
   opAt 942 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
