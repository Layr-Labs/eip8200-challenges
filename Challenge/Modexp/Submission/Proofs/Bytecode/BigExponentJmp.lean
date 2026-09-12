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
    Decode.isValidJumpDest submissionBytecode 327 = true :=
  Artifact.isValidJumpDest_index 286 (by rfl)



theorem jump58 :
    Decode.isValidJumpDest submissionBytecode 90 = true :=
  Artifact.isValidJumpDest_index 73 (by rfl)



theorem jump1039 :
    Decode.isValidJumpDest submissionBytecode 952 = true :=
  Artifact.isValidJumpDest_index 733 (by rfl)


theorem jump1090 :
    Decode.isValidJumpDest submissionBytecode 1003 = true :=
  Artifact.isValidJumpDest_index 772 (by rfl)


theorem jump963 :
    Decode.isValidJumpDest submissionBytecode 879 = true :=
  Artifact.isValidJumpDest_index 690 (by rfl)



theorem jump1104 :
    Decode.isValidJumpDest submissionBytecode 1017 = true :=
  Artifact.isValidJumpDest_index 783 (by rfl)


theorem jump946 :
    Decode.isValidJumpDest submissionBytecode 862 = true :=
  Artifact.isValidJumpDest_index 675 (by rfl)
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
