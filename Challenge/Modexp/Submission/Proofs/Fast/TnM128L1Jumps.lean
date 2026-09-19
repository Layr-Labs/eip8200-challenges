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
  · exact TnM128CandidateArtifact.isValidJumpDest_index 3060 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 3029 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2998 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2967 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2936 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2905 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2874 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2843 (by rfl)

theorem square_jump : Decode.isValidJumpDest TnM128Candidate.bytecode 4268 = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 3383 (by rfl)

#print axioms entry_jump
end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Jumps
