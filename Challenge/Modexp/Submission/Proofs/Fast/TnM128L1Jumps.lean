import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Steps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

theorem entry_jump (k : Nat) (hk : k ≤ 7) :
    Decode.isValidJumpDest TnM128Candidate.bytecode (3646-37*k) = true := by
  interval_cases k
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2733 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2702 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2671 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2640 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2609 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2578 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2547 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2516 (by rfl)

theorem square_jump : Decode.isValidJumpDest TnM128Candidate.bytecode 4093 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3059 (by rfl)

#print axioms entry_jump
end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
