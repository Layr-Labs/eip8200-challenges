import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! # Program-counter tables for the multi-limb exponentiation path

Kept in a module with minimal imports: `interval_cases … <;> decide` over these
ranges is elaborated far more cheaply without the whole `Big*` simp environment
in scope.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp

@[simp] theorem exponentPCs (i : Nat)
    (hi : 697 ≤ i) (hii : i ≤ 735) :
    Artifact.submissionArtifact.instructionPC i =
      ([892,893,894,895,896,897,898,899,902,903,904,905,906,907,908,909,910,911,912,914,915,916,917,920,921,923,924,925,927,928,929,930,933,934,935,938,941,944,947] : List Nat)[i - 697]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
