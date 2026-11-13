import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneSumsBase
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore

theorem pair128_nat_bound (lo hi : Nat)
    (hlo : lo < 2 ^ 128) (hhi : hi < 2 ^ 128) :
    lo + hi * 2 ^ 128 < 2 ^ 256 := by
  calc
    lo + hi * 2 ^ 128 < 2 ^ 128 + hi * 2 ^ 128 :=
      Nat.add_lt_add_right hlo _
    _ = (hi + 1) * 2 ^ 128 := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    _ ≤ 2 ^ 128 * 2 ^ 128 :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hhi)
    _ = 2 ^ 256 := by decide

#print axioms pair128_nat_bound

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore
