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
-- Current decoded SHA-256: 4ce91e1a71bb05b640d092f8b31b066d15468c05840194a8933e64dbc42c9df1.
-- 5238 bytes, 3615 instructions, 280 trailing data bytes; direct scorer 650681.
-- Backward snapshots preserve Ready by lanes/zeros/slack, not whole-memory equality.
-- Immediate 651113 predecessor: 0de279b7-dd75-4eb5-a010-f11bc5a46d10, accepted/promoted.
-- Canonical verification status is recorded in README.md; comments are not proof evidence.
