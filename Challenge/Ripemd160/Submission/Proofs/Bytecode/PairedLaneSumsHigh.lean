import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneSumsBounds
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore

theorem high_ofNat_pair (lo hi : Nat)
    (hlo : lo < 2 ^ 128) (hhi : hi < 2 ^ 128) :
    high (BitVec.ofNat 256 (lo + 2 ^ 128 * hi)) = BitVec.ofNat 32 hi := by
  have hcomm : lo + 2 ^ 128 * hi = lo + hi * 2 ^ 128 :=
    congrArg (fun n => lo + n) (Nat.mul_comm (2 ^ 128) hi)
  have hword : lo + 2 ^ 128 * hi < 2 ^ 256 :=
    hcomm.symm ▸ pair128_nat_bound lo hi hlo hhi
  apply BitVec.eq_of_toNat_eq
  change (((lo + 2 ^ 128 * hi) % 2 ^ 256) >>> 128) % 2 ^ 32 = hi % 2 ^ 32
  calc
    (((lo + 2 ^ 128 * hi) % 2 ^ 256) >>> 128) % 2 ^ 32 =
        ((lo + 2 ^ 128 * hi) >>> 128) % 2 ^ 32 :=
      congrArg (fun n => (n >>> 128) % 2 ^ 32) (Nat.mod_eq_of_lt hword)
    _ = ((lo + 2 ^ 128 * hi) / 2 ^ 128) % 2 ^ 32 := by
      rw [Nat.shiftRight_eq_div_pow]
    _ = (lo / 2 ^ 128 + hi) % 2 ^ 32 :=
      congrArg (fun n => n % 2 ^ 32) (Nat.add_mul_div_left lo hi (by decide))
    _ = hi % 2 ^ 32 := by
      rw [Nat.div_eq_of_lt hlo, Nat.zero_add]

#print axioms high_ofNat_pair
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore
