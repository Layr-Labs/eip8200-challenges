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
  · exact TnCandidateArtifact.isValidJumpDest_index 3015 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2984 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2953 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2922 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2891 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2860 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2829 (by rfl)
  · exact TnCandidateArtifact.isValidJumpDest_index 2798 (by rfl)

theorem square_jump : Decode.isValidJumpDest TnCandidate.bytecode 4471 = true :=
  TnCandidateArtifact.isValidJumpDest_index 3388 (by rfl)

#print axioms entry_jump
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateL1Jumps
