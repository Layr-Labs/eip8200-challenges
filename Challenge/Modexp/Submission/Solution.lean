import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Correct
import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Correctness of the submitted MODEXP bytecode.

Instruction 0 enters the existing RSA-2048, RSA-1024, and RSA-257 exact
guards in sequence.  A fourth exact guard recognizes the 192-byte BN254
modular-inversion vector and returns its certified inverse; all other inputs
fall through to the existing fast path and reference body. -/
theorem candidate : Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode
  exact Challenge.Modexp.Submission.Proofs.Fast.Correct.submission_correct_of
    Challenge.Modexp.Submission.Proofs.Fast.Exp.gasSteps_handled

end Challenge.Modexp.Benchmark
