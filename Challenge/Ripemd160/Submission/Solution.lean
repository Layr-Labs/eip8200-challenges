import Challenge.Ripemd160.Benchmark.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Benchmark

/-- Exact-bytecode correctness for the direct stack-resident compressor. -/
theorem candidate : Challenge.Ripemd160.Correct bytecode := by
  change Challenge.Ripemd160.Correct Challenge.Ripemd160.submissionBytecode
  exact Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard.correct_of_recognition
    Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect.from_entry
      Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect.from_loaded1000

end Challenge.Ripemd160.Benchmark

#print axioms Challenge.Ripemd160.Benchmark.candidate
-- Current decoded SHA-256: 5733027944add81140248a79dc8c91db19a5d21df7eba06dafb12c6bd1181c44.
-- 9427 bytes; local seedscore 640427.
-- Direct literal-word scanner; final partial-word mask derived from calldata size.
