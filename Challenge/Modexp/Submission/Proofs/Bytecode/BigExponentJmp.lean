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
    Decode.isValidJumpDest submissionBytecode 298 = true :=
  Artifact.isValidJumpDest_index 264 (by rfl)



theorem jump58 :
    Decode.isValidJumpDest submissionBytecode 53 = true :=
  Artifact.isValidJumpDest_index 45 (by rfl)



theorem jump1039 :
    Decode.isValidJumpDest submissionBytecode 1001 = true :=
  Artifact.isValidJumpDest_index 772 (by rfl)


theorem jump1090 :
    Decode.isValidJumpDest submissionBytecode 1052 = true :=
  Artifact.isValidJumpDest_index 811 (by rfl)


theorem jump963 :
    Decode.isValidJumpDest submissionBytecode 926 = true :=
  Artifact.isValidJumpDest_index 729 (by rfl)



theorem jump1104 :
    Decode.isValidJumpDest submissionBytecode 1066 = true :=
  Artifact.isValidJumpDest_index 822 (by rfl)


theorem jump946 :
    Decode.isValidJumpDest submissionBytecode 909 = true :=
  Artifact.isValidJumpDest_index 714 (by rfl)
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
