import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376DigestSchedules
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Digest

open EvmSemantics.Crypto Patterned376InputData

theorem compress0 (h : Array UInt32) :
    Ripemd160.compressBlock h paddedLiteral 0 =
      CompressionCorrect.normalizedCompress h block0 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule0]

theorem compress1 (h : Array UInt32) :
    Ripemd160.compressBlock h paddedLiteral 64 =
      CompressionCorrect.normalizedCompress h block1 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule1]

theorem compress2 (h : Array UInt32) :
    Ripemd160.compressBlock h paddedLiteral 128 =
      CompressionCorrect.normalizedCompress h block2 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule2]

theorem compress3 (h : Array UInt32) :
    Ripemd160.compressBlock h paddedLiteral 192 =
      CompressionCorrect.normalizedCompress h block3 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule3]

theorem compress4 (h : Array UInt32) :
    Ripemd160.compressBlock h paddedLiteral 256 =
      CompressionCorrect.normalizedCompress h block4 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule4]

theorem compress5 (h : Array UInt32) :
    Ripemd160.compressBlock h paddedLiteral 320 =
      CompressionCorrect.normalizedCompress h block5 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule5]

theorem compress6 (h : Array UInt32) :
    Ripemd160.compressBlock h paddedLiteral 384 =
      CompressionCorrect.normalizedCompress h block6 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule6]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Digest
