import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShape

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificates
open PoolShape

theorem lane_sources : ∀ j : Fin 61, ∀ k : Fin 4,
    resultSource false (18*j.val+10+k.val) = resultSource true (18*j.val+10+k.val) ∧
    resultSource false (18*j.val+28+k.val) = resultSource true (18*j.val+28+k.val) := by decide

theorem clear_sources : ∀ a ∈ zeroAddresses, resultSource false a = .zero := by decide

theorem terminal_sources : ∀ k : Fin 32,
    resultSource false (594+k.val) = resultSource true (594+k.val) := by decide

/-- Slots 42, 46 and 50 are re-witnessed at byte 22: word 9 is no longer masked
by S51, so it now occupies byte 14 of those three slots.  Byte 22 is zero under
both the masked and the unmasked pool, so this array also validates the clean
image. -/
def zeroByte : Array Nat := #[14,14,14,14,14,26,14,14,14,18,14,22,18,14,14,14,14,14,18,14,14,14,14,14,14,26,14,14,14,14,14,26,14,14,14,18,14,18,14,14,14,26,22,14,14,14,22,14,14,14,22,14,26,14,14,14,14,14,14,22,14]

theorem slack_sources : ∀ j : Fin 61,
    14 ≤ zeroByte[j.val]! ∧ zeroByte[j.val]! ≤ 26 ∧
    resultSource false (18*j.val+zeroByte[j.val]!) = .zero := by decide

theorem zeroAddresses_bound : ∀ a ∈ zeroAddresses, a < 1056 := by decide

theorem writes_bound : ∀ x ∈ writes, x.1+32 ≤ 1112 ∧ x.2 < 16 := by decide

#print axioms lane_sources
#print axioms slack_sources
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificates
