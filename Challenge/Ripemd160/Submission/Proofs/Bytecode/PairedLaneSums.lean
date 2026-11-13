import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneSumsNormalize
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore

theorem normalize_four_adds (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32) :
    normalize (((pack a0 b0 + pack a1 b1) + pack a2 b2) + pack a3 b3) =
      pack (((a0 + a1) + a2) + a3) (((b0 + b1) + b2) + b3) := by
  rw [pack_eq_ofNat a0 b0, pack_eq_ofNat a1 b1,
    pack_eq_ofNat a2 b2, pack_eq_ofNat a3 b3]
  simp only [BitVec.ofNat_add_ofNat]
  have hsplit :
      (((a0.toNat + b0.toNat * 2 ^ 128) +
        (a1.toNat + b1.toNat * 2 ^ 128)) +
        (a2.toNat + b2.toNat * 2 ^ 128)) +
        (a3.toNat + b3.toNat * 2 ^ 128) =
      (a0.toNat + a1.toNat + a2.toNat + a3.toNat) +
        (b0.toNat + b1.toNat + b2.toNat + b3.toNat) * 2 ^ 128 := by
    simp only [Nat.add_mul]
    omega
  rw [hsplit, normalize_ofNat]
  · simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have h0 := a0.isLt
    have h1 := a1.isLt
    have h2 := a2.isLt
    have h3 := a3.isLt
    simp only [Nat.reducePow] at *
    omega
  · have h0 := b0.isLt
    have h1 := b1.isLt
    have h2 := b2.isLt
    have h3 := b3.isLt
    simp only [Nat.reducePow] at *
    omega

theorem and_four_adds (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32) :
    (((pack a0 b0 + pack a1 b1) + pack a2 b2) + pack a3 b3) &&& pairMask =
      pack (((a0 + a1) + a2) + a3) (((b0 + b1) + b2) + b3) := by
  rw [← normalize_eq_and]
  exact normalize_four_adds a0 a1 a2 a3 b0 b1 b2 b3


#print axioms normalize_four_adds
#print axioms and_four_adds
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore
