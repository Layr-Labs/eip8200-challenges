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
-- Current decoded SHA-256: 92d8625df624bc564f501de855a0a6523f2bde22027508298760a38157bd797a.
-- 5238 bytes, 3616 instructions, 280 trailing data bytes; direct scorer 651239.
-- Immediate base: PC792 submission 8eb88703 (651365), remote validation pending.
-- ScratchSnapshotMemory proves exact pool/full memory equality for arbitrary memory.
-- Both normal and 32-byte bootstrap paths compose the same writer state at826.
-- Only byte interval527..554 changes; endpoints, chunks, downstream PCs and data stay fixed.
-- Whole-program canonical verification is authoritative; vector tests are not a proof.
