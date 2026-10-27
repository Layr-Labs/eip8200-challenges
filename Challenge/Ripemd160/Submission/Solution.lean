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

/-- Exact-byte universal RIPEMD-160 correctness, including the specialised
pad-only prefix, the round-48 resident-key fold, both outcomes of both 1000-byte
recognizers, and every inherited compressor/serialization path. -/
theorem candidate : Challenge.Ripemd160.Correct bytecode :=
  bytecode_eq_submission.symm ▸ Submission.Proofs.Bytecode.HoistedStoreCorrect.correct

end Challenge.Ripemd160.Benchmark

#print axioms Challenge.Ripemd160.Benchmark.candidate
-- Decoded SHA-256: f5a544656f69df166d5a86069bbd024c7a6a312a406baba6048aa96700abf33a.
-- 9742 bytes, 5258 instructions. Specialised pad-only prefix.
-- Only the protected benchmark is authoritative for correctness and gas.
