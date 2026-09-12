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

theorem jump310 :
    Decode.isValidJumpDest submissionBytecode 281 = true :=
  Artifact.isValidJumpDest_index 253 (by rfl)



theorem jump58 :
    Decode.isValidJumpDest submissionBytecode 46 = true :=
  Artifact.isValidJumpDest_index 40 (by rfl)



theorem jump1039 :
    Decode.isValidJumpDest submissionBytecode 906 = true :=
  Artifact.isValidJumpDest_index 700 (by rfl)


theorem jump1090 :
    Decode.isValidJumpDest submissionBytecode 957 = true :=
  Artifact.isValidJumpDest_index 739 (by rfl)


theorem jump963 :
    Decode.isValidJumpDest submissionBytecode 833 = true :=
  Artifact.isValidJumpDest_index 657 (by rfl)



theorem jump1104 :
    Decode.isValidJumpDest submissionBytecode 971 = true :=
  Artifact.isValidJumpDest_index 750 (by rfl)


theorem jump946 :
    Decode.isValidJumpDest submissionBytecode 816 = true :=
  Artifact.isValidJumpDest_index 642 (by rfl)
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
