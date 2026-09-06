import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestB

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestC

open PatternedDigest

theorem step8 : CompressionCorrect.normalizedCompress H8 block8 = H9 := by decide
theorem step9 : CompressionCorrect.normalizedCompress H9 block9 = H10 := by decide
theorem step10 : CompressionCorrect.normalizedCompress H10 block10 = H11 := by decide
theorem step11 : CompressionCorrect.normalizedCompress H11 block11 = H12 := by decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestC
