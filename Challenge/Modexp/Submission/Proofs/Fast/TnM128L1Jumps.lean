import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Steps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

theorem entry_jump (k : Nat) (hk : k ≤ 7) :
    Decode.isValidJumpDest TnM128Candidate.bytecode (3838-37*k) = true := by
  interval_cases k
  · exact TnM128CandidateArtifact.isValidJumpDest_index 3002 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2971 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2940 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2909 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2878 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2847 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2816 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2785 (by rfl)

theorem square_jump : Decode.isValidJumpDest TnM128Candidate.bytecode 4245 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3325 (by rfl)

#print axioms entry_jump
end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
