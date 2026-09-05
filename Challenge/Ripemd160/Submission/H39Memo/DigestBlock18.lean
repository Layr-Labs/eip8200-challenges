import Challenge.Ripemd160.Submission.H39Memo.DigestData

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

theorem block18 : Proofs.Bytecode.CompressionCorrect.normalizedCompress HIn18 B18 = HOut18 := by decide

end Challenge.Ripemd160.Submission.H39Memo

