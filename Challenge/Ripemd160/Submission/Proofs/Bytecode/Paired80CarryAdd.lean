import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Carry

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Carry

open Paired80Core

/-- Quotient residue addition only needs absence of a carry across bit 80. -/
theorem high_add_nat (n e f : Nat)
    (hcarry : n % 2 ^ 80 + e < 2 ^ 80) :
    (((n + (e + 2 ^ 80 * f)) % 2 ^ 256) / 2 ^ 80) % 2 ^ 32 =
      (n / 2 ^ 80 % 2 ^ 32 + f) % 2 ^ 32 := by
  simp only [Nat.reducePow] at *
  omega

/-- Other spacer bits may be arbitrary; only the proven bit-48 gap is needed. -/
theorem normalize_add_pack (x : BitVec 256) (e f : BitVec 32)
    (hgap : x.getLsbD 48 = false) :
    normalize (x + pack e f) = pack (low x + e) (high x + f) := by
  have hgap' : (x.extractLsb' 0 80).getLsbD 48 = false := by
    simpa only [BitVec.getLsbD_extractLsb', Nat.zero_add,
      show decide (48 < 80) = true from rfl, Bool.true_and] using hgap
  have hcarry := add32_no_carry80 (x.extractLsb' 0 80) e hgap'
  have hcarryNat : x.toNat % 2 ^ 80 + e.toNat < 2 ^ 80 := by
    simpa only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] using hcarry
  have hp : (pack e f).toNat = e.toNat + 2 ^ 80 * f.toNat := by
    calc
      (pack e f).toNat = e.toNat + f.toNat * 2 ^ 80 := pack_toNat e f
      _ = e.toNat + 2 ^ 80 * f.toNat :=
        congrArg (fun n => e.toNat + n) (Nat.mul_comm f.toNat (2 ^ 80))
  have hlo : low (x + pack e f) = low x + e := by
    change (x + pack e f).extractLsb' 0 32 = low x + e
    rw [BitVec.extractLsb'_add (by decide)]
    exact congrArg (fun y => low x + y) (low_pack e f)
  have hhi : high (x + pack e f) = high x + f := by
    apply BitVec.eq_of_toNat_eq
    simp only [high, BitVec.extractLsb'_toNat, BitVec.toNat_add, hp,
      Nat.shiftRight_eq_div_pow]
    exact high_add_nat x.toNat e.toNat f.toNat hcarryNat
  exact congr (congrArg pack hlo) hhi

#print axioms high_add_nat
#print axioms normalize_add_pack

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Carry
