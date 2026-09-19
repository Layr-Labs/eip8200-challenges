import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Steps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

theorem entry_jump (k : Nat) (hk : k ≤ 7) :
    Decode.isValidJumpDest TnM128Candidate.bytecode (3831-37*k) = true := by
  interval_cases k
  · exact TnM128CandidateArtifact.isValidJumpDest_index 3063 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 3032 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 3001 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2970 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2939 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2908 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2877 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2846 (by rfl)

theorem square_jump : Decode.isValidJumpDest TnM128Candidate.bytecode 4268 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3379 (by rfl)

#print axioms entry_jump
end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
