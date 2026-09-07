import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestA

open PatternedDigest

theorem step0 : CompressionCorrect.normalizedCompress H0 block0 = H1 := by decide
theorem step1 : CompressionCorrect.normalizedCompress H1 block1 = H2 := by decide
theorem step2 : CompressionCorrect.normalizedCompress H2 block2 = H3 := by decide
theorem step3 : CompressionCorrect.normalizedCompress H3 block3 = H4 := by decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestA
