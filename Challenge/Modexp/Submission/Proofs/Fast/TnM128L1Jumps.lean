import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Steps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

theorem entry_jump (k : Nat) (hk : k ≤ 7) :
    Decode.isValidJumpDest TnM128Candidate.bytecode (3606-37*k) = true := by
  interval_cases k
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2815 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2784 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2753 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2722 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2691 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2660 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2629 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2598 (by rfl)

theorem square_jump : Decode.isValidJumpDest TnM128Candidate.bytecode 5297 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 4219 (by rfl)

#print axioms entry_jump
end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
