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
pad-only prefix through paired round15, the round-48 resident-key fold, both outcomes of both 1000-byte
recognizers, and every inherited compressor/serialization path. -/
theorem candidate : Challenge.Ripemd160.Correct bytecode :=
  bytecode_eq_submission.symm ▸ Submission.Proofs.Bytecode.HoistedStoreCorrect.correct

end Challenge.Ripemd160.Benchmark

#print axioms Challenge.Ripemd160.Benchmark.candidate
-- Decoded SHA-256: 6eb386e046706e667a1c95a78154905844c35b29d796d1163622a3a52f87bb4d.
-- 9909 bytes, 5372 instructions. Specialised pad-only prefix through round15.
-- Only the protected benchmark is authoritative for correctness and gas.
