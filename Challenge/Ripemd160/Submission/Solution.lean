import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreCorrect
import Challenge.Ripemd160.Benchmark.Artifact

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Benchmark

/-- The protected literal is the very image used in the universal execution proof.
This is kernel definitional equality, not a digest or length comparison. -/
private theorem bytecode_eq_submission :
    bytecode = Submission.Proofs.Bytecode.HoistedInherited.submissionBytecode := by
  rfl

/-- Exact-byte universal RIPEMD-160 correctness, including the full pad-only
copy of the compressor, the compact patterned arms behind the size dispatcher,
both outcomes of both 1000-byte recognizers, and every inherited
compressor/serialization path. -/
theorem candidate : Challenge.Ripemd160.Correct bytecode :=
  bytecode_eq_submission.symm ▸ Submission.Proofs.Bytecode.HoistedStoreCorrect.correct

end Challenge.Ripemd160.Benchmark

#print axioms Challenge.Ripemd160.Benchmark.candidate
-- Decoded SHA-256: 4b6cc04e20e9f6ef12e7b217d1b59d6edc6873f60abd2d00a4d245b6fad37250.
-- 10264 bytes, 7037 instructions. Full pad-only compressor copy with word-0 key folds, compact arms.
-- Only the protected benchmark is authoritative for correctness and gas.
