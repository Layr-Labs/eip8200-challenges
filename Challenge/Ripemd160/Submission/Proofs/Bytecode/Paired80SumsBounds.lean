import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80SumsBase
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Core

theorem pair80_nat_bound (lo hi : Nat)
    (hlo : lo < 2 ^ 80) (hhi : hi < 2 ^ 80) :
    lo + hi * 2 ^ 80 < 2 ^ 256 := by
  calc
    lo + hi * 2 ^ 80 < 2 ^ 80 + hi * 2 ^ 80 :=
      Nat.add_lt_add_right hlo _
    _ = (hi + 1) * 2 ^ 80 := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    _ ≤ 2 ^ 80 * 2 ^ 80 :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hhi)
    _ < 2 ^ 256 := by decide

#print axioms pair80_nat_bound

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Core
