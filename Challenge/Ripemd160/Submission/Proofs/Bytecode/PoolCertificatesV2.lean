import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShapeV2

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificatesV2
open PoolShape PoolShapeV2

/-- Both lanes of every slot agree with the clean reference image, and the reference's lane
terms read no memory at all, so the two images agree whatever either base holds. -/
theorem lane_sources : ∀ j : Fin 61, ∀ k : Fin 4,
    resultSourceV2 (18*j.val+10+k.val) = resultSource true (18*j.val+10+k.val) ∧
    resultSourceV2 (18*j.val+28+k.val) = resultSource true (18*j.val+28+k.val) ∧
    Source.memFree (resultSource true (18*j.val+10+k.val)) = true ∧
    Source.memFree (resultSource true (18*j.val+28+k.val)) = true := by decide

theorem clear_sources : ∀ a ∈ zeroAddressesV2, resultSourceV2 a = .zero := by decide

/-- One provably-zero byte among word bytes 14..26 of every slot: word 11's masked gap or one
of the bytes the single stores and four copies leave zero in a raw word's gap. -/
def zeroByte : Array Nat := #[18,26,14,26,26,26,22,14,16,18,14,22,18,16,14,14,14,14,18,14,18,14,26,18,14,26,22,22,22,26,22,26,14,14,14,18,14,18,18,14,22,26,22,14,22,14,22,14,14,14,22,14,26,14,14,14,14,14,18,22,22]

theorem slack_sources : ∀ j : Fin 61,
    14 ≤ zeroByte[j.val]! ∧ zeroByte[j.val]! ≤ 26 ∧
    resultSourceV2 (18*j.val+zeroByte[j.val]!) = .zero := by decide

#print axioms lane_sources
#print axioms slack_sources
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificatesV2
