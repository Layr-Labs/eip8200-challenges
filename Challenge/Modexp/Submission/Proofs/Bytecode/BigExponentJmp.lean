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
    Decode.isValidJumpDest submissionBytecode 299 = true :=
  Artifact.isValidJumpDest_index 265 (by rfl)



theorem jump58 :
    Decode.isValidJumpDest submissionBytecode 54 = true :=
  Artifact.isValidJumpDest_index 46 (by rfl)



theorem jump1039 :
    Decode.isValidJumpDest submissionBytecode 986 = true :=
  Artifact.isValidJumpDest_index 757 (by rfl)


theorem jump1090 :
    Decode.isValidJumpDest submissionBytecode 1037 = true :=
  Artifact.isValidJumpDest_index 796 (by rfl)


theorem jump963 :
    Decode.isValidJumpDest submissionBytecode 911 = true :=
  Artifact.isValidJumpDest_index 714 (by rfl)



theorem jump1104 :
    Decode.isValidJumpDest submissionBytecode 1051 = true :=
  Artifact.isValidJumpDest_index 807 (by rfl)


theorem jump946 :
    Decode.isValidJumpDest submissionBytecode 894 = true :=
  Artifact.isValidJumpDest_index 699 (by rfl)
end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
