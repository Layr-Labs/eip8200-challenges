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
-- Current executable SHA-256: 133fb927006677692a6e1222da300a3b5a716484cbe449ff4b96fb5d1360cee0.
-- 5248 bytes, 3626 instructions, 280 data bytes; protected direct scorer 651533.
-- Base: promoted f797f38b / source 82d85410 (651617).
-- PC738 replaces PUSH2 738; adjacent wider pushes preserve byte endpoints.
-- PC666 stores word14 earlier across six disjoint memory windows. Fixed-PC
-- hypotheses and complete writer memory are proved, not assumed relocatable.
-- Integrated full proof/canonical gate remain the authoritative verification.
