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
-- Current decoded SHA-256: d103f31d4724be75c9093d6ebd398ba06a66d19144f901095a67793cea2da51f.
-- 5238 bytes, 3616 instructions, 280 trailing data bytes; direct scorer 651407.
-- Immediate base: promoted e1007b50 (651491), with inherited PC162/666/738 stores.
-- Mask only the terminal schedule store at address594 and remove byte610 clear.
-- FusedTerminalMemory and both schedule-entry execution paths maintain Ready.
-- CODESIZE exit sentinel is5238; memory-start offset remains1056.
-- Whole-program canonical verification is authoritative; vector tests are not a proof.
