import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 160000
set_option maxHeartbeats 16000000
/-! # Program-counter tables for the multi-limb exponentiation path

Kept in a module with minimal imports: `interval_cases … <;> decide` over these
ranges is elaborated far more cheaply without the whole `Big*` simp environment
in scope.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp

@[simp] theorem selectPCs (i : Nat)
    (hi : 700 ≤ i) (hii : i ≤ 749) :
    Artifact.submissionArtifact.instructionPC i =
      ([906,907,908,909,910,911,914,915,916,918,919,920,923,924,925,926,929,930,931,932,933,934,935,936,937,938,939,942,943,944,945,946,947,949,950,951,952,953,956,957,958,959,960,961,963,964,965,966,967,970] : List Nat)[i - 700]! := by
  interval_cases i <;> decide
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
