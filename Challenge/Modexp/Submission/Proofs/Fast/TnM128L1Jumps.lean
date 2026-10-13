import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Steps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

theorem entry_jump (k : Nat) (hk : k ≤ 7) :
    Decode.isValidJumpDest TnM128Candidate.bytecode (3849-37*k) = true := by
  interval_cases k
  · exact TnM128CandidateArtifact.isValidJumpDest_index 3014 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2983 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2952 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2921 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2890 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2859 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2828 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2797 (by rfl)

theorem square_jump : Decode.isValidJumpDest TnM128Candidate.bytecode 4259 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3325 (by rfl)

#print axioms entry_jump
end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
