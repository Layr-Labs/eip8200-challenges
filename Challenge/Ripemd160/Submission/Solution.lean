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
-- Current executable SHA-256: b9182bbcc8258af8bc5e754e1c71c7c0fa52275e282da7d02049f55fe926e095.
-- 5248 bytes, 3626 instructions, 280 data bytes; trusted-scorer total 651575.
-- Base: promoted f797f38b / source 82d85410 (651617).
-- At PC 738 the schedule writer uses PC instead of PUSH2 738 (one gas saved
-- per invocation); adjacent PUSH2s become PUSH3s to preserve later PCs and indices.
-- Paired73 commutes its AND operand duplicates to fit the trusted byte literal
-- budget. The final theorem still covers arbitrary valid calldata, not just vectors.
