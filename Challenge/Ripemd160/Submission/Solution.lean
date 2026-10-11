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
-- Current decoded SHA-256: 769cf37a78c18560c27bca378656587f554998b1da3d551f389eea51dd523b9d.
-- 5238 bytes, 3616 instructions, 280 trailing data bytes; direct scorer 651365.
-- Immediate base: promoted 7d82d5fd (651407), retaining PC162/666/738 and terminal mask.
-- Pc792Writer proves exact execution, 34-to-35 active-word growth, and masked-image equality.
-- Only byte interval606..826 changes; endpoints, chunks, downstream PCs and data stay fixed.
-- Whole-program canonical verification is authoritative; vector tests are not a proof.
