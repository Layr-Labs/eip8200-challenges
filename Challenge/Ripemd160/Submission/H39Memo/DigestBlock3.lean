import Challenge.Ripemd160.Submission.H39Memo.DigestData

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

theorem block3 : Proofs.Bytecode.CompressionCorrect.normalizedCompress HIn3 B3 = HOut3 := by decide

end Challenge.Ripemd160.Submission.H39Memo

