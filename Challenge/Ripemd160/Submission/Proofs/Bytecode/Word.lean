import Challenge.EvmProof.Word
import Mathlib.Tactic.IntervalCases
set_option warningAsError true
/-!
# RIPEMD-160 operations as EVM word expressions

These expressions mirror the reference Yul helpers.  They form the reusable
word-level boundary for the direct bytecode proof: once the EVM operands are
known to be embedded 32-bit words, the lemmas below rewrite an opcode result
to the corresponding operation in `EvmSemantics.Crypto.Ripemd160`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Word

open EvmSemantics
open Challenge.EvmProof.Word

abbrev EWord := EvmSemantics.UInt256

@[simp] theorem add_zero (a : EWord) : a + 0 = a := by
  apply word_ext
  change (a.val + 0).val = a.val.val
  simp

theorem land_comm (a b : EWord) : UInt256.land a b = UInt256.land b a := by
  apply word_ext
  rw [word_toNat_land, word_toNat_land, Nat.and_comm]

theorem lor_comm (a b : EWord) : UInt256.lor a b = UInt256.lor b a := by
  apply word_ext
  rw [word_toNat_lor, word_toNat_lor, Nat.or_comm]

def evmRotl32 (x : EWord) (n : Nat) : EWord :=
  mask32 (UInt256.shiftLeft x (UInt256.ofNat n) |||
    UInt256.shiftRight x (UInt256.ofNat (32 - n)))

def evmF (j : Nat) (x y z : EWord) : EWord :=
  match j with
  | 0 => (x ^^^ y) ^^^ z
  | 1 => (x &&& y) ||| (~~~x &&& z)
  | 2 => mask32 ((x ||| ~~~y) ^^^ z)
  | 3 => (x &&& z) ||| (y &&& ~~~z)
  | _ => mask32 (x ^^^ (y ||| ~~~z))

@[simp] theorem evmRotl32_ofUInt32 (x : UInt32) (n : Nat)
    (hn0 : 0 < n) (hn : n < 32) :
    evmRotl32 (ofUInt32 x) n =
      ofUInt32 (Crypto.Ripemd160.rotl32 x n) := by
  exact Challenge.EvmProof.Word.evm_rotl32 x n hn0 hn

private theorem notAnd_ofUInt32 (x z : UInt32) :
    (~~~ofUInt32 x) &&& ofUInt32 z =
      ofUInt32 (Crypto.Ripemd160.bnot32 x &&& z) := by
  rw [and_ofUInt32, toUInt32_not_ofUInt32]
  rfl

private theorem andNot_ofUInt32 (x z : UInt32) :
    ofUInt32 x &&& ~~~ofUInt32 z =
      ofUInt32 (x &&& Crypto.Ripemd160.bnot32 z) := by
  have hcomm : ofUInt32 x &&& ~~~ofUInt32 z =
      (~~~ofUInt32 z) &&& ofUInt32 x := by
    apply word_ext
    change ((ofUInt32 x).val &&& (~~~ofUInt32 z).val).val =
      ((~~~ofUInt32 z).val &&& (ofUInt32 x).val).val
    rw [Fin.and_val, Fin.and_val, Nat.and_comm]
  rw [hcomm, and_ofUInt32, toUInt32_not_ofUInt32]
  apply congrArg ofUInt32
  unfold Crypto.Ripemd160.bnot32
  rw [UInt32.and_comm]

@[simp] theorem evmF_ofUInt32 (j : Nat) (x y z : UInt32) (hj : j < 5) :
    evmF j (ofUInt32 x) (ofUInt32 y) (ofUInt32 z) =
      ofUInt32 (Crypto.Ripemd160.f j x y z) := by
  interval_cases j <;>
    simp only [evmF, Crypto.Ripemd160.f]
  · rw [← ofUInt32_xor, ← ofUInt32_xor]
  · rw [notAnd_ofUInt32, ← ofUInt32_and, ← ofUInt32_or]
  · rw [mask32_xor, toUInt32_or, toUInt32_ofUInt32,
      toUInt32_not_ofUInt32, toUInt32_ofUInt32]
    rfl
  · rw [andNot_ofUInt32, ← ofUInt32_and, ← ofUInt32_or]
  · rw [mask32_xor, toUInt32_or, toUInt32_ofUInt32,
      toUInt32_not_ofUInt32, toUInt32_ofUInt32]
    rfl

theorem or_eq_add_of_lt {a n B : Nat} (hB : B < 2 ^ n) :
    (a * 2 ^ n) ||| B = a * 2 ^ n + B := by
  have hpow : 0 < 2 ^ n := Nat.two_pow_pos n
  have hq : ((a * 2 ^ n) ||| B) / 2 ^ n = a := by
    rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_or_distrib,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mul_div_cancel _ hpow, Nat.div_eq_of_lt hB, Nat.or_zero]
  have hr : ((a * 2 ^ n) ||| B) % 2 ^ n = B := by
    rw [Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.mod_eq_of_lt hB, Nat.zero_or]
  have h := Nat.div_add_mod ((a * 2 ^ n) ||| B) (2 ^ n)
  rw [hq, hr] at h
  rw [← h, Nat.mul_comm]

/-- `SHL(y, n)` followed by `ADD(., SHR(., 32))` is the `SHL/SHR/OR` rotation
idiom, exactly, for a 32-bit `y` and `n ≤ 32`.  The two operands are disjoint:
`y <<< n` has its low `n` bits clear and `(y <<< n) >>> 32 = y >>> (32 - n) < 2 ^ n`. -/
theorem shiftLeft_add_shiftRight32 (y : UInt256) (n : Nat)
    (hy : y.toNat < 2 ^ 32) (hn : n ≤ 32) :
    UInt256.shiftLeft y (UInt256.ofNat n) +
      UInt256.shiftRight (UInt256.shiftLeft y (UInt256.ofNat n)) (UInt256.ofNat 32) =
    UInt256.lor (UInt256.shiftLeft y (UInt256.ofNat n))
      (UInt256.shiftRight y (UInt256.ofNat (32 - n))) := by
  set v := y.toNat with hv
  have hv256 : v < 2 ^ 256 := Nat.lt_trans hy (by norm_num)
  have hn256 : n < 256 := by omega
  have hpn : (2 : Nat) ^ n ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hn
  have hA64 : v * 2 ^ n < 2 ^ 64 := by
    calc v * 2 ^ n < 2 ^ 32 * 2 ^ n := by exact (Nat.mul_lt_mul_right (Nat.two_pow_pos n)).mpr hy
    _ ≤ 2 ^ 32 * 2 ^ 32 := Nat.mul_le_mul_left _ hpn
    _ = 2 ^ 64 := by norm_num
  have hA : v * 2 ^ n < 2 ^ 256 := Nat.lt_trans hA64 (by norm_num)
  have hyeq : y = UInt256.ofNat v := word_eq_ofNat_toNat y
  -- the two shifted operands
  have hshl : UInt256.shiftLeft y (UInt256.ofNat n) = UInt256.ofNat (v * 2 ^ n) := by
    rw [hyeq]; exact shiftLeft_ofNat hv256 hn256 hA
  have hsplit : (2 : Nat) ^ 32 = 2 ^ n * 2 ^ (32 - n) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hshr32 : (v * 2 ^ n) >>> 32 = v >>> (32 - n) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hsplit, Nat.mul_comm v (2 ^ n),
      Nat.mul_div_mul_left _ _ (Nat.two_pow_pos n)]
  have hBlt : v >>> (32 - n) < 2 ^ n := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm]; rw [← hsplit] at *; exact hy
  have hB32 : v >>> (32 - n) < 2 ^ 32 := Nat.lt_of_lt_of_le hBlt hpn
  have hsum : v * 2 ^ n + v >>> (32 - n) < 2 ^ 256 := by
    have h1 : v * 2 ^ n < 2 ^ 64 := hA64
    have h2 : (2:Nat) ^ 64 + 2 ^ 32 < 2 ^ 256 := by norm_num
    omega
  have hB256 : v >>> (32 - n) < 2 ^ 256 := by
    have : (2:Nat) ^ 32 < 2 ^ 256 := by norm_num
    omega
  rw [hshl, shiftRight_ofNat hA (by norm_num), hshr32, hyeq,
    shiftRight_ofNat hv256 (by omega), ofNat_add_ofNat hsum]
  apply word_ext
  rw [word_toNat_lor, word_toNat_ofNat, word_toNat_ofNat, word_toNat_ofNat,
    Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB256, or_eq_add_of_lt hBlt,
    Nat.mod_eq_of_lt hsum]

theorem mask32_toNat_lt (q : UInt256) : (mask32 q).toNat < 2 ^ 32 := by
  rw [mask32_toNat, show (0xffffffff : Nat) = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

/-- The form the helper templates meet: the rotated operand is the result of
`PUSH4 0xffffffff; AND`, so its 32-bit bound holds by construction. -/
theorem masked_shiftLeft_add_shiftRight32 (q : UInt256) (n : Nat) (hn : n ≤ 32) :
    UInt256.shiftLeft (mask32 q) (UInt256.ofNat n) +
      UInt256.shiftRight
        (UInt256.shiftLeft (mask32 q) (UInt256.ofNat n)) (UInt256.ofNat 32) =
    UInt256.lor (UInt256.shiftLeft (mask32 q) (UInt256.ofNat n))
      (UInt256.shiftRight (mask32 q) (UInt256.ofNat (32 - n))) :=
  shiftLeft_add_shiftRight32 (mask32 q) n (mask32_toNat_lt q) hn


/-- `UInt256.add`-shaped restatement, matching the term the helper trace
simp produces. -/
theorem masked_shiftLeft_add_shiftRight32_add (q : EWord) (n : Nat) (hn : n <= 32) :
    UInt256.add (UInt256.shiftLeft (mask32 q) (UInt256.ofNat n))
      (UInt256.shiftRight
        (UInt256.shiftLeft (mask32 q) (UInt256.ofNat n)) (UInt256.ofNat 32)) =
    UInt256.lor (UInt256.shiftLeft (mask32 q) (UInt256.ofNat n))
      (UInt256.shiftRight (mask32 q) (UInt256.ofNat (32 - n))) :=
  masked_shiftLeft_add_shiftRight32 q n hn

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
