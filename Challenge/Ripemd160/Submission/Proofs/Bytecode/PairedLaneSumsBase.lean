import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore

theorem pack_toNat (lo hi : BitVec 32) :
    (pack lo hi).toNat = lo.toNat + hi.toNat * 2 ^ 128 := by
  unfold pack
  rw [BitVec.toNat_append,
    BitVec.toNat_setWidth_of_le (by decide),
    BitVec.toNat_setWidth_of_le (by decide)]
  have hlow : lo.toNat < 2 ^ 128 := by
    have := lo.isLt
    simp only [Nat.reducePow] at *
    omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hlow, Nat.shiftLeft_eq, Nat.add_comm]

theorem pack_eq_ofNat (lo hi : BitVec 32) :
    pack lo hi = BitVec.ofNat 256 (lo.toNat + hi.toNat * 2 ^ 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat, BitVec.toNat_ofNat]
  apply (Nat.mod_eq_of_lt _).symm
  have hlo := lo.isLt
  have hhi := hi.isLt
  simp only [Nat.reducePow] at *
  omega

#print axioms pack_toNat
#print axioms pack_eq_ofNat
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore
