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
-- Current decoded SHA-256: 34b57b79b00486b64a85666336c9e0e48c9822c2fc925bda08ccb3222c17c9c5.
-- 5247 bytes, 3617 executable instructions; local replica 647222 clean/dirty (record 647411, newjordan d62f7e87).
-- Built on newjordan's d62f7e87 (direct empty/abc return) and 52f50e76 (round-75 filler removed, PUSH13 -> PUSH14);
-- adds kaankolcu's window 62-72 cut with its own filler replaced by a PUSH13 -> PUSH14 widening in round 71, and
-- gas-neutral rewrites in rounds 9-17 and 44-51.
