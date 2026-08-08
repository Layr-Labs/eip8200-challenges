import Challenge.Sha256.Benchmark.Artifact
import Challenge.Sha256.Submission.Proofs.Bytecode.ReferenceCorrect

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Sha256.Benchmark

/-- Correctness of the direct-entry SHA-256 bytecode candidate. -/
theorem candidate : Challenge.Sha256.Correct bytecode := by
  change Challenge.Sha256.Correct Challenge.Sha256.submissionBytecode
  exact Challenge.Sha256.Submission.Proofs.Bytecode.ReferenceCorrect.reference_correct

end Challenge.Sha256.Benchmark
