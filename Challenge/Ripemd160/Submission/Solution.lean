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
-- Current decoded SHA-256: cf1f1a482b2838cf29be047a9e12f17111868ce0ea36eb3603341afefb411703.
-- 9715 bytes; low64 shifted-XOR anchor, generic continuation relocated to 222.
-- The protected benchmark, not these comments, is the score and correctness authority.
