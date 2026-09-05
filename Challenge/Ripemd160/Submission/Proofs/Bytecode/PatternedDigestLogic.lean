import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestD

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem schedule0 : CompressionCorrect.schedule patternedInput 0 = block0 := by decide
theorem schedule1 : CompressionCorrect.schedule patternedInput 64 = block1 := by decide
theorem schedule2 : CompressionCorrect.schedule patternedInput 128 = block2 := by decide
theorem schedule3 : CompressionCorrect.schedule patternedInput 192 = block3 := by decide
theorem schedule4 : CompressionCorrect.schedule patternedInput 256 = block4 := by decide
theorem schedule5 : CompressionCorrect.schedule patternedInput 320 = block5 := by decide
theorem schedule6 : CompressionCorrect.schedule patternedInput 384 = block6 := by decide
theorem schedule7 : CompressionCorrect.schedule patternedInput 448 = block7 := by decide
theorem schedule8 : CompressionCorrect.schedule patternedInput 512 = block8 := by decide
theorem schedule9 : CompressionCorrect.schedule patternedInput 576 = block9 := by decide
theorem schedule10 : CompressionCorrect.schedule patternedInput 640 = block10 := by decide
theorem schedule11 : CompressionCorrect.schedule patternedInput 704 = block11 := by decide
theorem schedule12 : CompressionCorrect.schedule patternedInput 768 = block12 := by decide
theorem schedule13 : CompressionCorrect.schedule patternedInput 832 = block13 := by decide
theorem schedule14 : CompressionCorrect.schedule patternedInput 896 = block14 := by decide
theorem schedule_final : CompressionCorrect.schedule finalBlock 0 = finalWords := by decide

theorem compress0 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 0 =
      CompressionCorrect.normalizedCompress h block0 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule0]
theorem compress1 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 64 =
      CompressionCorrect.normalizedCompress h block1 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule1]
theorem compress2 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 128 =
      CompressionCorrect.normalizedCompress h block2 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule2]
theorem compress3 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 192 =
      CompressionCorrect.normalizedCompress h block3 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule3]
theorem compress4 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 256 =
      CompressionCorrect.normalizedCompress h block4 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule4]
theorem compress5 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 320 =
      CompressionCorrect.normalizedCompress h block5 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule5]
theorem compress6 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 384 =
      CompressionCorrect.normalizedCompress h block6 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule6]
theorem compress7 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 448 =
      CompressionCorrect.normalizedCompress h block7 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule7]
theorem compress8 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 512 =
      CompressionCorrect.normalizedCompress h block8 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule8]
theorem compress9 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 576 =
      CompressionCorrect.normalizedCompress h block9 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule9]
theorem compress10 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 640 =
      CompressionCorrect.normalizedCompress h block10 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule10]
theorem compress11 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 704 =
      CompressionCorrect.normalizedCompress h block11 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule11]
theorem compress12 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 768 =
      CompressionCorrect.normalizedCompress h block12 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule12]
theorem compress13 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 832 =
      CompressionCorrect.normalizedCompress h block13 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule13]
theorem compress14 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 896 =
      CompressionCorrect.normalizedCompress h block14 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule14]
theorem compress_final (h : Array UInt32) :
    Ripemd160.compressBlock h finalBlock 0 =
      CompressionCorrect.normalizedCompress h finalWords := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule_final]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
