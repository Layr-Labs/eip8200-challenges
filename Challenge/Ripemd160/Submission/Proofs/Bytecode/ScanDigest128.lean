import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Digest
set_option warningAsError true
set_option maxRecDepth 100000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest128
abbrev paddedDigest := Patterned128Digest.paddedDigest
abbrev paddedDigestWord := Patterned128Digest.paddedDigestWord
theorem data_eq : ShortPatternLogic.data128 = Patterned128Data.data := by decide
theorem spec_pattern : Challenge.Ripemd160.spec ShortPatternLogic.data128 = paddedDigest := by
  rw [data_eq]
  exact Patterned128Digest.spec_data_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest128
