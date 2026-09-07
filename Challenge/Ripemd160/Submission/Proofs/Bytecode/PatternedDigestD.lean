import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestC

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestD

open PatternedDigest

theorem step12 : CompressionCorrect.normalizedCompress H12 block12 = H13 := by decide
theorem step13 : CompressionCorrect.normalizedCompress H13 block13 = H14 := by decide
theorem step14 : CompressionCorrect.normalizedCompress H14 block14 = H15 := by decide
theorem step15 : CompressionCorrect.normalizedCompress H15 block15 = H16 := by decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestD
