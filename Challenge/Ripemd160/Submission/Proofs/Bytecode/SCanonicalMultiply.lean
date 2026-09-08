import Challenge.EvmProof.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge
import Init.Data.BitVec.Bitblast

set_option warningAsError true

/-!
Canonical 32-bit duplication by multiplication: Experiment S arithmetic.

For a canonical EVM word `x` with `x.toNat < 2 ^ 32`, multiplying by the
17-byte literal `R = 1 + 2 ^ 128` copies the low word into lanes `[0, 32)`
and `[128, 160)` with the product below `2 ^ 160`:

`x * R = x ||| (x << 128)` as exact full words, with no modular wrap.

The proof transfers to `BitVec 256` through `PairedLaneUInt256Bridge`,
splits the factor as `2 ^ 128 + 1`, and discharges the addition as a
bitwise OR by disjointness of the shifted copy. No decision procedure
over variables, axiom, `sorry`, or `native_decide` is used. All `Nat`
bounds use monotonicity of powers and `omega`; no `decide` above 256.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SCanonicalMultiply

open EvmSemantics PairedLaneUInt256Bridge

/-- The 17-byte duplication literal `R = 1 + 2 ^ 128` pushed by the S startup. -/
def dupFactor : UInt256 := UInt256.ofNat (1 + 2 ^ 128)

/-- `2 ^ 128 < 2 ^ 256`: small decides only, no giant evaluation. -/
private theorem pow128_lt_size : (2 ^ 128 : Nat) < 2 ^ 256 :=
  Nat.pow_lt_pow_right (by decide) (by decide)

/-- The literal fits in a word: derived from `pow128_lt_size` by `omega`. -/
private theorem dupLit_lt_size : (1 + 2 ^ 128 : Nat) < 2 ^ 256 := by
  have h := pow128_lt_size
  omega

theorem dupFactor_toNat : dupFactor.toNat = 1 + 2 ^ 128 := by
  unfold dupFactor
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt dupLit_lt_size]

#print axioms dupFactor_toNat

/-- A canonical 32-bit word has no bits at or above index 32. -/
private theorem getLsbD_eq_false_of_canonical (x : BitVec 256)
    (h : x.toNat < 2 ^ 32) {i : Nat} (hi : 32 ≤ i) :
    x.getLsbD i = false := by
  have hlt : x.toNat < 2 ^ i :=
    lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hi)
  have hbit : x.toNat.testBit i = false := Nat.testBit_lt_two_pow hlt
  rwa [BitVec.testBit_toNat] at hbit

/-- The 128-shifted copy of a canonical word is disjoint from the original. -/
private theorem shift128_disjoint (x : BitVec 256) (h : x.toNat < 2 ^ 32) :
    (x <<< 128) &&& x = 0#256 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  by_cases hlo : i < 128
  · simp [hlo]
  · have hx : x.getLsbD i = false :=
      getLsbD_eq_false_of_canonical x h (by omega)
    simp [hx]

/-- `twoPow 256 128` denotes `2 ^ 128`. -/
private theorem twoPow128_toNat : (BitVec.twoPow 256 128).toNat = 2 ^ 128 :=
  BitVec.toNat_twoPow_of_lt (by decide)

/-- Factor split by toNat congruence: no 256-bit `decide`. -/
private theorem factor_split :
    BitVec.ofNat 256 (1 + 2 ^ 128) = BitVec.twoPow 256 128 + 1#256 := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 256 (1 + 2 ^ 128)).toNat = 1 + 2 ^ 128 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt dupLit_lt_size]
  have h2 : (BitVec.twoPow 256 128 + 1#256).toNat = 1 + 2 ^ 128 := by
    rw [BitVec.toNat_add, BitVec.toNat_one (by decide), twoPow128_toNat,
      Nat.add_comm (2 ^ 128) 1, Nat.mod_eq_of_lt dupLit_lt_size]
  rw [h1, h2]

/-- Bit-vector form: scaling a canonical word by `1 + 2 ^ 128` copies it. -/
theorem bits_mul_dupFactor (x : BitVec 256) (h : x.toNat < 2 ^ 32) :
    x * BitVec.ofNat 256 (1 + 2 ^ 128) = (x <<< 128) ||| x := by
  rw [factor_split,
    BitVec.mul_add, BitVec.mul_twoPow_eq_shiftLeft, BitVec.mul_one]
  exact BitVec.add_eq_or_of_and_eq_zero _ _ (shift128_disjoint x h)

#print axioms bits_mul_dupFactor

/-- EVM-word form: `x * (1 + 2 ^ 128) = x OR (x << 128)` for canonical `x`. -/
theorem mul_dupFactor (x : UInt256) (h : x.toNat < 2 ^ 32) :
    UInt256.mul x dupFactor =
      UInt256.lor x (UInt256.shiftLeft x (UInt256.ofNat 128)) := by
  have hb : (bits x).toNat < 2 ^ 32 := by
    rw [bits_toNat]
    exact h
  have key := bits_mul_dupFactor (bits x) hb
  apply bits_injective
  unfold dupFactor
  rw [bits_mul, bits_ofNat, bits_lor, bits_shl x 128 (by decide),
    BitVec.or_comm]
  exact key

#print axioms mul_dupFactor

/-- Word multiply on toNat: `change` avoids unfolding `UInt256.size`. -/
private theorem mul_toNat (a b : UInt256) :
    (UInt256.mul a b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

/-- `2 ^ 32 * 2 ^ 128 = 2 ^ 160` by `pow_add`: no giant `decide`. -/
private theorem pow32_mul_pow128 : (2 ^ 32 : Nat) * 2 ^ 128 = 2 ^ 160 := by
  rw [← Nat.pow_add]

/-- `2 ^ 160 < 2 ^ 256`: small decides only. -/
private theorem pow160_lt_size : (2 ^ 160 : Nat) < 2 ^ 256 :=
  Nat.pow_lt_pow_right (by decide) (by decide)

/-- The duplication product stays below `2 ^ 160`: no modular wrap occurs. -/
theorem mul_dupFactor_toNat (x : UInt256) (h : x.toNat < 2 ^ 32) :
    (UInt256.mul x dupFactor).toNat < 2 ^ 160 := by
  have hle : (x.toNat + 1) * 2 ^ 128 ≤ 2 ^ 32 * 2 ^ 128 := by
    gcongr
    omega
  have heq1 : (x.toNat + 1) * 2 ^ 128 = x.toNat * 2 ^ 128 + 2 ^ 128 := by
    rw [Nat.add_mul, Nat.one_mul]
  have hexpand : x.toNat * (1 + 2 ^ 128) = x.toNat * 2 ^ 128 + x.toNat := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]
  have hprod : x.toNat * (1 + 2 ^ 128) < 2 ^ 160 := by
    rw [pow32_mul_pow128] at hle
    omega
  have hmul : (UInt256.mul x dupFactor).toNat =
      (x.toNat * dupFactor.toNat) % 2 ^ 256 := mul_toNat x dupFactor
  rw [hmul, dupFactor_toNat,
    Nat.mod_eq_of_lt (Nat.lt_trans hprod pow160_lt_size)]
  exact hprod

#print axioms mul_dupFactor_toNat

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SCanonicalMultiply
