import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateL1Steps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateL1Jumps
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

theorem entry_jump (k : Nat) (hk : k ≤ 7) :
    Decode.isValidJumpDest TnCandidate.bytecode (3999-37*k) = true := by
  interval_cases k
  · exact TnCandidateArtifact.isValidJumpDest_index 3004 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2973 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2942 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2911 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2880 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2849 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2818 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2787 (by rfl)

theorem square_jump : Decode.isValidJumpDest TnCandidate.bytecode 4471 = true :=
  TnCandidateArtifact.isValidJumpDest_index 3377 (by rfl)

#print axioms entry_jump
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateL1Jumps
