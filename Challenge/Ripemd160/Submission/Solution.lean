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
-- redraw marker 2026-09-15T09:15:23Z
-- Yukon reuse by @ercumentyildirim: source @i34-9, submission e1481dcc-c9a9-4364-82b3-0903851f0c06, commit 7a6785a7e139fe90f0d16f78b70221ae7926d355.
-- provenance marker TAIL412-v1
-- executable 61804baf7d0d6906621e2496f4323019a9be4896d8d2fd4fe04939960254b926, 5214 bytes, 664789 gas, derived from 9d219ee0aaae45eb613c3416fcee2499c4dd814c09ccaf34868714f4ba4ca962 at 664803 gas.
