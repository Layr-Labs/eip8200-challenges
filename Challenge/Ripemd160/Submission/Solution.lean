import Challenge.Ripemd160.Submission.Proofs.Bytecode.BytecodeBinding
import Challenge.Ripemd160.Benchmark.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Correct

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Benchmark

/-- Compose semantic correctness before expanding either bytecode literal. -/
private theorem submission_correct :
    Challenge.Ripemd160.Correct Challenge.Ripemd160.submissionBytecode :=
  Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard.correct_of_recognition
    Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect.from_entry
      RetainedActual115.from_loaded1000

/-- Bind the protected image once, outside the universal execution predicate. -/
private theorem bytecode_eq_submission :
    bytecode = Challenge.Ripemd160.submissionBytecode :=
  Challenge.Ripemd160.Submission.Proofs.Bytecode.BytecodeBinding.exact

/-- Exact-bytecode correctness for the direct stack-resident compressor. -/
theorem candidate : Challenge.Ripemd160.Correct bytecode :=
  bytecode_eq_submission.symm ▸ submission_correct

end Challenge.Ripemd160.Benchmark

#print axioms Challenge.Ripemd160.Benchmark.candidate
-- Current decoded SHA-256: 8cd1e0bc824982ce5c93a50e7ff46b24c78d332b0029c0daa128146e194a6cac.
-- 9742 bytes; direct-shift abc guard and universally proved fullword scan coverage.
-- Only the protected benchmark is authoritative for correctness and gas.
