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

/-- Exact-byte universal RIPEMD-160 correctness, including both outcomes of
both 1000-byte recognizers and every inherited compressor/serialization path. -/
theorem candidate : Challenge.Ripemd160.Correct bytecode :=
  bytecode_eq_submission.symm ▸ Submission.Proofs.Bytecode.HoistedStoreCorrect.correct

end Challenge.Ripemd160.Benchmark

#print axioms Challenge.Ripemd160.Benchmark.candidate
-- Decoded SHA-256: fd29aa8c61320a5d6c839368fe558801e6629669bebc87b9e1439f3491449dd9.
-- 9742 bytes, 5429 instructions. Hoisted digest store and memory-size return.
-- Only the protected benchmark is authoritative for correctness and gas.
