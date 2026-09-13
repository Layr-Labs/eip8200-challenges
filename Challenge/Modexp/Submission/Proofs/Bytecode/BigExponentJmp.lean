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
    Decode.isValidJumpDest submissionBytecode 416 = true :=
  Artifact.isValidJumpDest_index 328 (by rfl)



theorem jump58 :
    Decode.isValidJumpDest submissionBytecode 177 = true :=
  Artifact.isValidJumpDest_index 115 (by rfl)



theorem jump1039 :
    Decode.isValidJumpDest submissionBytecode 1041 = true :=
  Artifact.isValidJumpDest_index 775 (by rfl)


theorem jump1090 :
    Decode.isValidJumpDest submissionBytecode 1092 = true :=
  Artifact.isValidJumpDest_index 814 (by rfl)


theorem jump963 :
    Decode.isValidJumpDest submissionBytecode 968 = true :=
  Artifact.isValidJumpDest_index 732 (by rfl)



theorem jump1104 :
    Decode.isValidJumpDest submissionBytecode 1106 = true :=
  Artifact.isValidJumpDest_index 825 (by rfl)


theorem jump946 :
    Decode.isValidJumpDest submissionBytecode 951 = true :=
  Artifact.isValidJumpDest_index 717 (by rfl)
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
