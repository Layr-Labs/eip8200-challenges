import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80SumsBounds
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Core

theorem low_ofNat_pair (lo hi : Nat)
    (_hlo : lo < 2 ^ 80) (_hhi : hi < 2 ^ 80) :
    low (BitVec.ofNat 256 (lo + 2 ^ 80 * hi)) = BitVec.ofNat 32 lo := by
  unfold low
  rw [← BitVec.setWidth_eq_extractLsb' (by decide),
    BitVec.setWidth_ofNat_of_le (by decide)]
  apply BitVec.eq_of_toNat_eq
  change (lo + 2 ^ 80 * hi) % 2 ^ 32 = lo % 2 ^ 32
  have hrem : 2 ^ 80 % 2 ^ 32 = 0 := by decide
  calc
    (lo + 2 ^ 80 * hi) % 2 ^ 32 =
        (lo % 2 ^ 32 + (2 ^ 80 * hi) % 2 ^ 32) % 2 ^ 32 :=
      Nat.add_mod _ _ _
    _ = (lo % 2 ^ 32 + ((2 ^ 80 % 2 ^ 32) * (hi % 2 ^ 32)) % 2 ^ 32) % 2 ^ 32 :=
      congrArg (fun n => (lo % 2 ^ 32 + n) % 2 ^ 32) (Nat.mul_mod _ _ _)
    _ = lo % 2 ^ 32 := by
      rw [hrem, Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]

#print axioms low_ofNat_pair
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Core
