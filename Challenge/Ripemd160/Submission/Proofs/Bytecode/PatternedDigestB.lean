import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestA

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestB

open PatternedDigest

theorem step4 : CompressionCorrect.normalizedCompress H4 block4 = H5 := by decide
theorem step5 : CompressionCorrect.normalizedCompress H5 block5 = H6 := by decide
theorem step6 : CompressionCorrect.normalizedCompress H6 block6 = H7 := by decide
theorem step7 : CompressionCorrect.normalizedCompress H7 block7 = H8 := by decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestB
