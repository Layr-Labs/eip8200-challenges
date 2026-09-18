import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShapeV2

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificatesV2
open PoolShape PoolShapeV2

/-- Both lanes of every slot agree with the clean reference image. -/
theorem lane_sources : ∀ j : Fin 61, ∀ k : Fin 4,
    resultSourceV2 (18*j.val+10+k.val) = resultSource true (18*j.val+10+k.val) ∧
    resultSourceV2 (18*j.val+28+k.val) = resultSource true (18*j.val+28+k.val) := by decide

theorem clear_sources : ∀ a ∈ zeroAddresses, resultSourceV2 a = .zero := by decide

theorem terminal_sources : ∀ k : Fin 32,
    resultSourceV2 (594+k.val) = resultSource true (594+k.val) := by decide

/-- One provably-zero byte among word bytes 14..26 of every slot.  Slot 2 (address 36) is
witnessed at byte 18, i.e. table byte 54: the raw word 0 stored at 54 carries the incoming
byte 0 there, which `Clear` now requires to be zero. -/
def zeroByte : Array Nat := #[14,14,18,26,14,26,14,14,14,18,14,22,18,14,14,14,14,14,18,14,18,14,14,14,14,26,22,14,22,26,22,26,14,14,14,18,14,18,14,14,14,26,22,14,22,14,22,14,14,14,22,14,26,14,14,14,14,14,14,22,14]

theorem slack_sources : ∀ j : Fin 61,
    14 ≤ zeroByte[j.val]! ∧ zeroByte[j.val]! ≤ 26 ∧
    resultSourceV2 (18*j.val+zeroByte[j.val]!) = .zero := by decide

#print axioms lane_sources
#print axioms slack_sources
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificatesV2
