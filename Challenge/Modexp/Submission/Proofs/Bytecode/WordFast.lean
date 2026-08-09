/-
Arithmetic core for a faster one-word MODEXP path (`modexpWord`).

RESTORED FROM CONTEXT after the scratchpad wipe.  The original lived at
scratchpad/wordpath/WordFast.lean and had been verified there (EXIT=0, zero
errors, permitted axioms only).  This copy is byte-for-byte what I read from
that file; it has NOT been re-verified since the wipe.

Everything here is bytecode-independent Nat arithmetic: the algorithmic changes
to the word path, each reduced to a statement a bytecode proof can discharge
its loop invariant against.

  1.  `two_pow_256_mod`     -- `R := addmod(mod(not 0, m), 1, m)` is `2^256 mod m`
  2.  `baseLoop_correct`    -- the word-at-a-time base Horner loop
  3.  `branchBitAfter_spec` -- square-and-multiply with a *branch* on the bit
  4.  `windowByte_spec`     -- one exponent byte as two 4-bit windows
  5.  `expAfter_spec`, `wordPath_modPow` -- either exponent loop reaches
      `Precompile.modPow`
  6.  `skipZeroByte`        -- soundness of the leading-zero-byte (`started`)
      skip

Imports mirror `Challenge/Modexp/Submission/Proofs/Algorithm.lean`, which is
already in the submission's import closure, plus `Challenge.EvmProof.Bytes`,
which the word path already imports transitively through `Word.lean`.  So
dropping this file into the proof tree adds no new import edge.
-/
import Challenge.Modexp.Submission.Proofs.Algorithm
import Challenge.EvmProof.Bytes
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring

namespace WordFast

open EvmSemantics
open EvmSemantics.EVM

/-! ## 1. The radix constant

The base Horner loop needs `2^256 mod m`.  The EVM cannot name `2^256`, but
`not(0)` is `2^256 - 1`, so

    R := addmod(mod(not(0), m), 1, m)

computes it in two opcodes.  Correct for every `m`; nothing about the size or
shape of `m` is used. -/

/-- `((radix - 1) mod m + 1) mod m = radix mod m` for any positive `radix`. -/
theorem radix_mod (radix m : Nat) (hradix : 0 < radix) :
    ((radix - 1) % m + 1) % m = radix % m := by
  rw [Nat.mod_add_mod]
  congr 1
  omega

/-- The instance the bytecode uses: `mod(not 0, m)` then `addmod(_, 1, m)`. -/
theorem two_pow_256_mod (m : Nat) :
    ((2 ^ 256 - 1) % m + 1) % m = 2 ^ 256 % m :=
  radix_mod _ m (Nat.pow_pos (by norm_num))

/-- The alternative spelling `addmod(mulmod(sub(0,1), 1, m), 1, m)` agrees, so
the two differ only in cost (`MOD` is 5 gas, `MULMOD` is 8). -/
theorem two_pow_256_mod' (m : Nat) :
    (((2 ^ 256 - 1) * 1) % m + 1) % m = 2 ^ 256 % m := by
  rw [Nat.mul_one]; exact two_pow_256_mod m

/-! ## 2. Word-at-a-time base Horner

The reference reduces the base one byte at a time,
`base := addmod(mulmod(base, 256, m), B[i], m)`, i.e. `bsize` iterations.
Consuming a full 32-byte word per iteration needs `bsize / 32` iterations plus
one leading partial word of `bsize mod 32` bytes. -/

/-- Appending the next full 32-byte word to a big-endian byte string multiplies
its value by `2^256`.  An instance of `bytesToNatPadded_add`. -/
theorem horner_split (input : ByteArray) (off n : Nat) :
    Precompile.bytesToNatPadded input off (n + 32) =
      Precompile.bytesToNatPadded input off n * 2 ^ 256 +
        Precompile.bytesToNatPadded input (off + n) 32 := by
  rw [Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  norm_num

/-- The accumulator of the word-at-a-time base loop: the leading `r`-byte
partial word, then `k` full words.  `radix` is whatever the bytecode holds for
`2^256 mod m`; the specification only constrains it modulo `m`. -/
def hornerAfter (input : ByteArray) (off r m radix : Nat) : Nat → Nat
  | 0 => Precompile.bytesToNatPadded input off r % m
  | k + 1 =>
      (hornerAfter input off r m radix k * radix % m +
        Precompile.bytesToNatPadded input (off + (r + 32 * k)) 32) % m

/-- **The base loop is correct.**  After `k` full words the accumulator holds
the first `r + 32k` bytes of the operand, reduced. -/
theorem hornerAfter_spec (input : ByteArray) (off r m radix : Nat)
    (hradix : radix % m = 2 ^ 256 % m) (k : Nat) :
    hornerAfter input off r m radix k =
      Precompile.bytesToNatPadded input off (r + 32 * k) % m := by
  induction k with
  | zero => simp [hornerAfter]
  | succ k ih =>
      have key : (Precompile.bytesToNatPadded input off (r + 32 * k) % m *
            radix) % m =
          (Precompile.bytesToNatPadded input off (r + 32 * k) * 2 ^ 256) % m := by
        rw [Nat.mul_mod, Nat.mod_mod, hradix, ← Nat.mul_mod]
      have hsplit := horner_split input off (r + 32 * k)
      rw [hornerAfter, ih, Nat.add_mod, key, ← Nat.add_mod,
        show r + 32 * (k + 1) = (r + 32 * k) + 32 by ring, hsplit]
      exact Nat.mod_add_mod _ _ _

/-- The loop as the bytecode runs it: `bsize mod 32` leading bytes, then
`bsize / 32` full words, reproduces the whole operand. -/
theorem baseLoop_correct (input : ByteArray) (off m radix bsize : Nat)
    (hradix : radix % m = 2 ^ 256 % m) :
    hornerAfter input off (bsize % 32) m radix (bsize / 32) =
      Precompile.bytesToNatPadded input off bsize % m := by
  rw [hornerAfter_spec input off (bsize % 32) m radix hradix (bsize / 32)]
  congr 2
  omega

/-! ## 3. Square-and-multiply with a branch

The reference always evaluates `product := mulmod(square, base, m)` and then
selects branchlessly.  Branching instead is sound because the two `if` arms are
exactly the two values the branchless select can produce; this model is
therefore definitionally `WordCorrect.natBitStep`, and the closed form below is
`WordCorrect.natBitAfter_eq`, reproved here so this file stands alone. -/

/-- One bit of the exponent, MSB-first within a byte. -/
def bitOf (w j : Nat) : Nat := w / 2 ^ (7 - j) % 2

/-- Value of the first `j` bits of a byte, MSB-first. -/
def bitPrefix (w : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => 2 * bitPrefix w j + bitOf w j

/-- The branching bit step: square, and multiply only when the bit is set. -/
def branchBitStep (m b w j acc : Nat) : Nat :=
  if bitOf w j = 0 then acc * acc % m else acc * acc % m * b % m

def branchBitAfter (m b w : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | j + 1, acc => branchBitStep m b w j (branchBitAfter m b w j acc)

theorem bitOf_le_one (w j : Nat) : bitOf w j = 0 ∨ bitOf w j = 1 := by
  unfold bitOf; omega

/-- **The branching exponent loop is correct**: after `j` bits the accumulator
is `acc^(2^j) * b^(prefix)`, exactly as for the branchless reference. -/
theorem branchBitAfter_spec (m b w : Nat) (_hm : 0 < m) (j : Nat) (acc : Nat)
    (hacc : acc < m) :
    branchBitAfter m b w j acc = (acc ^ 2 ^ j * b ^ bitPrefix w j) % m := by
  induction j with
  | zero => simpa [branchBitAfter, bitPrefix] using (Nat.mod_eq_of_lt hacc).symm
  | succ j ih =>
      have hA2 :
          (acc ^ 2 ^ j * b ^ bitPrefix w j) * (acc ^ 2 ^ j * b ^ bitPrefix w j)
            = acc ^ 2 ^ (j + 1) * b ^ (2 * bitPrefix w j) := by
        rw [pow_succ, pow_mul, two_mul, pow_add]
        ring
      have hsq :
          (acc ^ 2 ^ j * b ^ bitPrefix w j) % m *
              ((acc ^ 2 ^ j * b ^ bitPrefix w j) % m) % m
            = (acc ^ 2 ^ (j + 1) * b ^ (2 * bitPrefix w j)) % m := by
        rw [← Nat.mul_mod, hA2]
      rw [branchBitAfter, ih, branchBitStep, bitPrefix]
      rcases bitOf_le_one w j with h | h
      · rw [if_pos h, hsq, h]
        simp
      · rw [if_neg (by omega), hsq, h]
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        congr 1
        rw [pow_succ]
        ring

/-! ## 4. Fixed 4-bit windows

The alternative exponent loop is branchless: with `T[k] = b^k mod m` tabulated
for `k < 16`, each exponent byte `w` costs four squarings, a multiply by
`T[w / 16]`, four more squarings, and a multiply by `T[w % 16]`. -/

/-- `n` successive modular squarings. -/
def sq (m : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => sq m n x * sq m n x % m

theorem sq_spec (m : Nat) (n x : Nat) (hx : x < m) :
    sq m n x = x ^ 2 ^ n % m := by
  induction n with
  | zero => simpa [sq] using (Nat.mod_eq_of_lt hx).symm
  | succ n ih =>
      rw [sq, ih, ← Nat.mul_mod, ← pow_add]
      congr 1
      rw [← two_mul, pow_succ]
      ring

/-- One exponent byte as two 4-bit windows. -/
def windowByte (m b acc w : Nat) : Nat :=
  sq m 4 (sq m 4 acc * (b ^ (w / 16) % m) % m) * (b ^ (w % 16) % m) % m

/-- **The windowed byte step equals the reference byte step.**  The right-hand
side is `WordCorrect.natExpStep` verbatim, so the whole bridge from
`natExpAfter` up to `Precompile.modPow` applies unchanged. -/
theorem windowByte_spec (m b acc w : Nat) (hm : 0 < m) (hacc : acc < m) :
    windowByte m b acc w = (acc ^ 256 * b ^ w) % m := by
  have hsq : sq m 4 acc = acc ^ 16 % m := by
    simpa using sq_spec m 4 acc hacc
  have hmid : sq m 4 acc * (b ^ (w / 16) % m) % m
      = (acc ^ 16 * b ^ (w / 16)) % m := by
    rw [hsq, ← Nat.mul_mod]
  have hlt : (acc ^ 16 * b ^ (w / 16)) % m < m := Nat.mod_lt _ hm
  have hsq2 : sq m 4 ((acc ^ 16 * b ^ (w / 16)) % m)
      = (acc ^ 16 * b ^ (w / 16)) ^ 16 % m := by
    rw [sq_spec m 4 _ hlt]
    norm_num
    rw [← Nat.pow_mod]
  unfold windowByte
  rw [hmid, hsq2, ← Nat.mul_mod]
  congr 1
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
  congr 2
  omega

/-! ## 5. Both exponent loops reach `Precompile.modPow` -/

/-- Either loop's per-byte semantics: `acc^256 * b^byte`. -/
def expStep (m b acc w : Nat) : Nat := (acc ^ 256 * b ^ w) % m

def expAfter (input : ByteArray) (expOff m b : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc =>
      expStep m b (expAfter input expOff m b i acc)
        (Precompile.bytesToNatPadded input (expOff + i) 1)

/-- Base-256 digit accumulation: after `count` exponent bytes the accumulator
is `acc^(256^count) * b^(value of those bytes)`. -/
theorem expAfter_spec (input : ByteArray) (expOff m b : Nat)
    (count acc : Nat) (hacc : acc < m) :
    expAfter input expOff m b count acc =
      (acc ^ 256 ^ count *
        b ^ Precompile.bytesToNatPadded input expOff count) % m := by
  induction count with
  | zero => simpa [expAfter] using (Nat.mod_eq_of_lt hacc).symm
  | succ count ih =>
      have hdigits :=
        Challenge.EvmProof.Bytes.bytesToNatPadded_add input expOff count 1
      have hpow : ((acc ^ 256 ^ count *
            b ^ Precompile.bytesToNatPadded input expOff count) % m) ^ 256 % m
          = (acc ^ 256 ^ count *
            b ^ Precompile.bytesToNatPadded input expOff count) ^ 256 % m := by
        rw [← Nat.pow_mod]
      rw [expAfter, ih, expStep, Nat.mul_mod, hpow, ← Nat.mul_mod, hdigits]
      congr 1
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
      norm_num [pow_succ]

/-- `1 mod m` raised to any power is `1 mod m` (including `m = 1`, where both
sides are `0`). -/
theorem one_mod_pow (m k : Nat) (hm : 0 < m) : (1 % m) ^ k % m = 1 % m := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have hm1 : m = 1 := by omega
    subst hm1
    exact Nat.mod_one _
  · have h1 : 1 % m = 1 := Nat.mod_eq_of_lt h
    rw [h1, one_pow, h1]

/-- **The word path computes the precompile.**  Starting from `acc = 1 mod m`
and a base already reduced to `b mod m`, the accumulated
`acc^(256^count) * (b mod m)^e` is `Precompile.modPow b e m`. -/
theorem wordPath_modPow (b e m count : Nat) (hm : 0 < m) :
    ((1 % m) ^ 256 ^ count * (b % m) ^ e) % m = Precompile.modPow b e m := by
  rw [Challenge.Modexp.Submission.Proofs.Algorithm.modPow_eq, if_neg (by omega : ¬ m = 0)]
  rw [Nat.mul_mod, one_mod_pow m _ hm, ← Nat.pow_mod]
  rcases Nat.lt_or_ge m 2 with h | h
  · have hm1 : m = 1 := by omega
    subst hm1
    simp only [Nat.mod_one]
  · rw [Nat.mod_eq_of_lt h, Nat.one_mul, Nat.mod_mod]

/-! ## 6. The leading-zero-byte (`started`) skip

Skipping a leading zero exponent byte is sound because the accumulator is still
`1 mod m` and stays there: `(1 mod m)^256 * b^0 ≡ 1 mod m`.  This is *only*
sound while every exponent bit consumed so far is zero -- which is exactly the
`started = 0 ↔ prefix = 0` invariant of `ExpCore.accAfter_spec`. -/

theorem skipZeroByte (m b : Nat) (hm : 0 < m) :
    expStep m b (1 % m) 0 = 1 % m := by
  rw [expStep, pow_zero, Nat.mul_one, one_mod_pow m _ hm]

/-! ## 7. The guard the word path keys on

`modulusSize ≤ 32` bounds the modulus *value* below `2^256`, which is what the
one-word path needs.  The converse direction is the standing trap: a declared
size gives no lower bound on the value (`Msize = 40` may still carry `m = 3`),
so no shortcut may be keyed on the declared size. -/

theorem modulusValue_lt_of_size_le (input : ByteArray) (off width : Nat)
    (hwidth : width ≤ 32) :
    Precompile.bytesToNatPadded input off width < 2 ^ 256 := by
  refine lt_of_lt_of_le
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input off width) ?_
  calc (256 : Nat) ^ width ≤ 256 ^ 32 :=
        Nat.pow_le_pow_right (by norm_num) hwidth
    _ = 2 ^ 256 := by norm_num

end WordFast
