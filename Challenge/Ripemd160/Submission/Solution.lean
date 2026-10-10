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
-- Current executable SHA-256: 8a49a304e7a86d884c3cd0aeee9f2968721963853c96c771a43c2b4f129fa5e3.
-- 5248 bytes, 3626 instructions, 280 data bytes; protected direct scorer 651491.
-- Base: promoted f797f38b / source 82d85410 (651617).
-- PC738 replaces PUSH2 738; adjacent wider pushes preserve byte endpoints.
-- PC666 stores word14 earlier across six disjoint memory windows. Fixed-PC
-- hypotheses and complete writer memory are proved, not assumed relocatable.
-- Integrated full proof/canonical gate remain the authoritative verification.
-- PC162 pads the fast route with an early PUSH19 mark and a widened PUSH4 666.
-- Store order is unchanged; the raw theorem requires the actual entry PC130.

-- CODESIZE replaces the padding mark duplicate as the exit sentinel; the fast
-- branch-local input bound proves limit < 5248. Padding memory is unchanged.
