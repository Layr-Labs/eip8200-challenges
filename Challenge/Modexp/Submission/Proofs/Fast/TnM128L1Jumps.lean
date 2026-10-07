import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Steps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

theorem entry_jump (k : Nat) (hk : k ≤ 7) :
    Decode.isValidJumpDest TnM128Candidate.bytecode (3821-37*k) = true := by
  interval_cases k
  · exact TnM128CandidateArtifact.isValidJumpDest_index 3047 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 3016 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2985 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2954 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2923 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2892 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2861 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2830 (by rfl)

theorem square_jump : Decode.isValidJumpDest TnM128Candidate.bytecode 4258 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3372 (by rfl)

#print axioms entry_jump
end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
