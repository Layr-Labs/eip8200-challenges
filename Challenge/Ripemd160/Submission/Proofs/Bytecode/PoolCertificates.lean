import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShape

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificates
open PoolShape

theorem zeroAddresses_bound : ∀ a ∈ zeroAddresses, a < 1056 := by decide

theorem writes_bound : ∀ x ∈ writes, x.1+32 ≤ 1112 ∧ x.2 < 16 := by decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificates
