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
-- Current decoded SHA-256: 411fcad177dcd5a9cbe4f4c57b11ea5b51dc5680906f9670de9416c5b78dc37b.
-- 5260 bytes; trusted runtime 646095 clean/dirty, 98/98 checks.
-- Warm-empty guard + fixed nonfinal 40-bit tail projection.
-- Accepted and promoted by Yukon as ae929341-d1da-489c-8996-0776dea7b681:
-- official 646095 clean/dirty, verified=true, 49 vectors, state-independent gas.
