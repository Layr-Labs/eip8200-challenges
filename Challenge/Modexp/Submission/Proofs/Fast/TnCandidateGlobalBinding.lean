import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateArtifact
import Challenge.Modexp.Submission.Bytecode

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateGlobalBinding

theorem bytecode_eq : Challenge.Modexp.submissionBytecode = TnCandidate.bytecode := by rfl

#print axioms bytecode_eq
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateGlobalBinding
