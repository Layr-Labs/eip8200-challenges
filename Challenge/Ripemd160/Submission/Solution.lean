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
-- Current decoded SHA-256: c486a5354063d8a12260bfb53073962bad5ff88f7aeed6ff3b5b780b6a89e484.
-- 5238 bytes, 3614 instructions, 280 trailing data bytes; direct scorer 650666.
-- Backward snapshots preserve Ready by lanes/zeros/slack, not whole-memory equality.
-- Immediate 650681 predecessor: d6846540-c9d3-427a-84e0-cbe8c1bf15ac, accepted/promoted.
-- Canonical verification status is recorded in README.md; comments are not proof evidence.
