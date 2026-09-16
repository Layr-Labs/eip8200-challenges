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
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2727 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2696 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2665 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2634 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2603 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2572 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2541 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2510 (by rfl)

theorem square_jump : Decode.isValidJumpDest TnM128Candidate.bytecode 4093 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3053 (by rfl)

#print axioms entry_jump
end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
