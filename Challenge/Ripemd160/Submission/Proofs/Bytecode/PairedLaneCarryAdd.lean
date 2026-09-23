import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCarry

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCarry

open PairedLaneCore

/-- Quotient residue addition only needs absence of a carry across bit 128. -/
theorem high_add_nat (n e f : Nat)
    (hcarry : n % 2 ^ 128 + e < 2 ^ 128) :
    (((n + (e + 2 ^ 128 * f)) % 2 ^ 256) / 2 ^ 128) % 2 ^ 32 =
      (n / 2 ^ 128 % 2 ^ 32 + f) % 2 ^ 32 := by
  simp only [Nat.reducePow] at *
  omega

/-- Other spacer bits may be arbitrary; only the proven bit-64 gap is needed. -/
theorem normalize_add_pack (x : BitVec 256) (e f : BitVec 32)
    (hgap : x.getLsbD 64 = false) :
    normalize (x + pack e f) = pack (low x + e) (high x + f) := by
  have hgap' : (x.extractLsb' 0 128).getLsbD 64 = false := by
    simpa only [BitVec.getLsbD_extractLsb', Nat.zero_add,
      show decide (64 < 128) = true from rfl, Bool.true_and] using hgap
  have hcarry := add32_no_carry128 (x.extractLsb' 0 128) e hgap'
  have hcarryNat : x.toNat % 2 ^ 128 + e.toNat < 2 ^ 128 := by
    simpa only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] using hcarry
  have hp : (pack e f).toNat = e.toNat + 2 ^ 128 * f.toNat := by
    calc
      (pack e f).toNat = e.toNat + f.toNat * 2 ^ 128 := pack_toNat e f
      _ = e.toNat + 2 ^ 128 * f.toNat :=
        congrArg (fun n => e.toNat + n) (Nat.mul_comm f.toNat (2 ^ 128))
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCarry
