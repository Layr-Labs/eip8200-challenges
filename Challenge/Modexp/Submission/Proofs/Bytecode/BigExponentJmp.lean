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
    Decode.isValidJumpDest submissionBytecode 334 = true :=
  Artifact.isValidJumpDest_index 291 (by rfl)



theorem jump58 :
    Decode.isValidJumpDest submissionBytecode 97 = true :=
  Artifact.isValidJumpDest_index 78 (by rfl)



theorem jump1039 :
    Decode.isValidJumpDest submissionBytecode 959 = true :=
  Artifact.isValidJumpDest_index 738 (by rfl)


theorem jump1090 :
    Decode.isValidJumpDest submissionBytecode 1010 = true :=
  Artifact.isValidJumpDest_index 777 (by rfl)


theorem jump963 :
    Decode.isValidJumpDest submissionBytecode 886 = true :=
  Artifact.isValidJumpDest_index 695 (by rfl)



theorem jump1104 :
    Decode.isValidJumpDest submissionBytecode 1024 = true :=
  Artifact.isValidJumpDest_index 788 (by rfl)


theorem jump946 :
    Decode.isValidJumpDest submissionBytecode 869 = true :=
  Artifact.isValidJumpDest_index 680 (by rfl)
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
