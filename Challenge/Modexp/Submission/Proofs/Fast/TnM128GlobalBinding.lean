import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Bytecode
set_option warningAsError true
set_option maxRecDepth 40000
namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128GlobalBinding
theorem bytecode_eq : Challenge.Modexp.submissionBytecode = TnM128Candidate.bytecode := by rfl
end Challenge.Modexp.Submission.Proofs.Fast.TnM128GlobalBinding
