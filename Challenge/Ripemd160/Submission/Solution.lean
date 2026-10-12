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

end Challenge.Ripemd160.Benchmark

#print axioms Challenge.Ripemd160.Benchmark.candidate
-- Current decoded SHA-256: 7ca8fa738efad590e12452a91148305b73a199ac375b2827835956249fa7a52f.
-- 5238 bytes, 3605 instructions; fresh canonical gate accepted at 649851 clean/dirty gas over 49 vectors.
