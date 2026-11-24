import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBytes

set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp

/-- The historical runtime used by the shared instruction proofs. -/
abbrev submissionBytes : ByteArray :=
  Submission.Proofs.Fast.TnM128Candidate.bytecode

@[simp] theorem submissionBytes_size : submissionBytes.size = 10915 :=
  Submission.Proofs.Fast.TnM128Candidate.bytecode_size

end Challenge.Modexp
