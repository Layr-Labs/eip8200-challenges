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

/-- One provably-zero byte among word bytes 14..26 of every slot: either a masked word's gap
or one of the two-byte holes the four copies leave in every raw word's gap. -/
def zeroByte : Array Nat := #[14,26,20,26,26,26,22,14,14,18,14,22,18,14,14,14,14,14,18,14,18,14,26,14,14,26,22,22,22,26,22,26,14,14,14,18,14,18,14,14,22,26,22,14,22,14,22,14,14,14,22,14,26,14,14,14,14,14,14,22,22]

theorem slack_sources : ∀ j : Fin 61,
    14 ≤ zeroByte[j.val]! ∧ zeroByte[j.val]! ≤ 26 ∧
    resultSourceV2 (18*j.val+zeroByte[j.val]!) = .zero := by decide

#print axioms lane_sources
#print axioms slack_sources
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificatesV2
