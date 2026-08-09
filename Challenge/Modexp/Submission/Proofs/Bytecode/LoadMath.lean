/-
# Arithmetic contract for the word-at-a-time `loadBigEndian`

Everything here is a statement about `Nat` values of byte windows.  Nothing
mentions memory, so it is exactly the part of the correctness argument that the
bytecode-level block proofs consume rather than re-derive.

Split out of the previous prototype's `HelpersMath.lean`, which covered both
`addMaskedMod` and `loadBigEndian`.  The `addMaskedMod` half (`ofLimbs`,
`fuse`, `subChain`, `useSub_correct`, `carryOut_word`, `borrowOut_word`) is
deliberately left behind: it only pays off while the bit-serial
double-and-add multiply still exists, and a Knuth-D divider retires that.

## The limb convention

The reference loader is

    for i in 0 .. len-1:
      reverse = len - 1 - i
      limb    = reverse / 32
      shift   = 8 * (reverse % 32)
      mstore(dst + 32*limb,
             or(mload(dst + 32*limb), byte(0, calldataload(off+i)) << shift))

so `reverse` is the *significance* of input byte `i`, and limb `k` -- the word
at `dst + 32k`, read with an ordinary big-endian `MLOAD` -- holds the input
bytes of significance `32k .. 32k+31`, with significance `32k+j` at bit `8j`.
Limbs are therefore little-endian ordered and each limb is a plain 256-bit
natural number:

    limb k = V / (2^256)^k % 2^256,   V = bytesToNatPadded calldata off len.

Three consequences, one lemma each:

* `limb_eq_window` -- for `32*(k+1) ≤ len` a full limb is one 32-byte window,
  the one `calldataload(off + len - 32*(k+1))` reads;
* `top_limb_eq_prefix` -- the single partial top limb (`r = len % 32 ≠ 0`) is
  the leading `r` bytes of the input;
* `window_shift_eq_prefix` -- and `calldataload(off) >> (8*(32-r))` is exactly
  those leading `r` bytes.

`limb_high_eq_zero` closes the frame: no limb at or above `⌈len/32⌉` carries
any value, which is why the replacement writing nothing there is sound.

`bytesToNatPadded` zero-pads past the end of the byte array, matching
`calldataload`'s zero-padding past `calldatasize()` and the reference's
`byte(0, calldataload(off+i))`, so short, absent and past-the-end calldata all
come out identical without a side condition.
-/
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.LoadMath

/-! ## Small arithmetic helpers -/

private theorem div_mul_add_of_lt (a b c : Nat) (hc : 0 < c) (hb : b < c) :
    (a * c + b) / c = a := by
  rw [Nat.mul_comm, Nat.mul_add_div hc, Nat.div_eq_of_lt hb, Nat.add_zero]

private theorem mod_mul_add_of_lt (a b c : Nat) (hb : b < c) :
    (a * c + b) % c = b := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

private theorem pow2_256_pow (k : Nat) : (2 ^ 256 : Nat) ^ k = 256 ^ (32 * k) := by
  rw [show (2 ^ 256 : Nat) = 256 ^ 32 by norm_num, ← pow_mul]

/-! ## The limb convention -/

open EvmSemantics.EVM.Precompile in
/-- **Full limb.**  For `32 * (k + 1) ≤ len`, limb `k` of the `len`-byte
big-endian input is exactly one 32-byte window, the one the replacement reads
with `calldataload(off + len - 32*(k+1))`. -/
theorem limb_eq_window (bs : ByteArray) (off len k : Nat) (hk : 32 * (k + 1) ≤ len) :
    bytesToNatPadded bs off len / (2 ^ 256) ^ k % 2 ^ 256 =
      bytesToNatPadded bs (off + (len - 32 * (k + 1))) 32 := by
  set H := len - 32 * (k + 1) with hH
  have h1 : bytesToNatPadded bs off len =
      bytesToNatPadded bs off (H + 32) * 256 ^ (32 * k) +
        bytesToNatPadded bs (off + (H + 32)) (32 * k) := by
    rw [show len = (H + 32) + 32 * k by omega]
    exact Challenge.EvmProof.Bytes.bytesToNatPadded_add bs off (H + 32) (32 * k)
  have h2 : bytesToNatPadded bs off (H + 32) =
      bytesToNatPadded bs off H * 256 ^ 32 + bytesToNatPadded bs (off + H) 32 :=
    Challenge.EvmProof.Bytes.bytesToNatPadded_add bs off H 32
  have hlow : bytesToNatPadded bs (off + (H + 32)) (32 * k) < 256 ^ (32 * k) :=
    Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
  have hwin : bytesToNatPadded bs (off + H) 32 < 256 ^ 32 :=
    Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
  rw [h1, pow2_256_pow,
    div_mul_add_of_lt _ _ _ (by positivity) hlow,
    h2, show (2 ^ 256 : Nat) = 256 ^ 32 by norm_num,
    mod_mul_add_of_lt _ _ _ hwin]

open EvmSemantics.EVM.Precompile in
/-- **Partial top limb.**  The top limb `len / 32` is the leading `len % 32`
bytes of the input, which the replacement obtains as
`calldataload(off) >> (8 * (32 - len % 32))`. -/
theorem top_limb_eq_prefix (bs : ByteArray) (off len : Nat) :
    bytesToNatPadded bs off len / (2 ^ 256) ^ (len / 32) =
      bytesToNatPadded bs off (len % 32) := by
  have h1 : bytesToNatPadded bs off len =
      bytesToNatPadded bs off (len % 32) * 256 ^ (32 * (len / 32)) +
        bytesToNatPadded bs (off + len % 32) (32 * (len / 32)) := by
    conv_lhs => rw [show len = len % 32 + 32 * (len / 32) by omega]
    exact Challenge.EvmProof.Bytes.bytesToNatPadded_add bs off (len % 32) _
  have hlow : bytesToNatPadded bs (off + len % 32) (32 * (len / 32)) <
      256 ^ (32 * (len / 32)) :=
    Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
  rw [h1, pow2_256_pow, div_mul_add_of_lt _ _ _ (by positivity) hlow]

open EvmSemantics.EVM.Precompile in
/-- `calldataload(off) >> (8 * (32 - r))` keeps the leading `r` bytes, for
`r ≤ 32`.  This is the only shift the replacement performs. -/
theorem window_shift_eq_prefix (bs : ByteArray) (off r : Nat) (hr : r ≤ 32) :
    bytesToNatPadded bs off 32 / 2 ^ (8 * (32 - r)) =
      bytesToNatPadded bs off r := by
  have h1 : bytesToNatPadded bs off 32 =
      bytesToNatPadded bs off r * 256 ^ (32 - r) +
        bytesToNatPadded bs (off + r) (32 - r) := by
    conv_lhs => rw [show (32 : Nat) = r + (32 - r) by omega]
    exact Challenge.EvmProof.Bytes.bytesToNatPadded_add bs off r (32 - r)
  have hlow : bytesToNatPadded bs (off + r) (32 - r) < 256 ^ (32 - r) :=
    Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
  have hpow : (2 : Nat) ^ (8 * (32 - r)) = 256 ^ (32 - r) := by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul]
  rw [h1, hpow, div_mul_add_of_lt _ _ _ (by positivity) hlow]

/-! ## The frame: which limbs the loader may leave alone -/

open EvmSemantics.EVM.Precompile in
/-- **Nothing above the top limb.**  If `len ≤ 32 * k` then limb `k` and every
limb above it is zero, so the replacement is entitled to write no destination
word at or beyond `dst + 32 * ⌈len/32⌉`. -/
theorem limb_high_eq_zero (bs : ByteArray) (off len k : Nat) (hk : len ≤ 32 * k) :
    bytesToNatPadded bs off len / (2 ^ 256) ^ k = 0 := by
  have hlt : bytesToNatPadded bs off len < 256 ^ len :=
    Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
  have hmono : (256 : Nat) ^ len ≤ 256 ^ (32 * k) :=
    Nat.pow_le_pow_right (by norm_num) hk
  exact Nat.div_eq_of_lt (by rw [pow2_256_pow]; omega)

open EvmSemantics.EVM.Precompile in
/-- The exact word the replacement's tail stores, in one step: for
`r = len % 32 ≠ 0` the top limb equals the shifted leading window. -/
theorem top_limb_eq_shifted_window (bs : ByteArray) (off len : Nat) :
    bytesToNatPadded bs off len / (2 ^ 256) ^ (len / 32) =
      bytesToNatPadded bs off 32 / 2 ^ (8 * (32 - len % 32)) := by
  rw [top_limb_eq_prefix, window_shift_eq_prefix bs off (len % 32) (by omega)]

open EvmSemantics.EVM.Precompile in
/-- The top limb is already reduced, so the `% 2^256` that the general limb
projection carries is a no-op there. -/
theorem top_limb_lt (bs : ByteArray) (off len : Nat) (hr : len % 32 ≠ 0) :
    bytesToNatPadded bs off len / (2 ^ 256) ^ (len / 32) < 2 ^ 256 := by
  rw [top_limb_eq_prefix]
  have h : bytesToNatPadded bs off (len % 32) < 256 ^ (len % 32) :=
    Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
  have hmono : (256 : Nat) ^ (len % 32) ≤ 256 ^ 32 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have : (256 : Nat) ^ 32 = 2 ^ 256 := by norm_num
  omega

/-! ## Every OR the replacement performs is against a cleared word

The word-at-a-time loop writes each destination limb exactly once, so an
`or(mload(at), v)` on a cleared destination is `0 ||| v = v`.  The stronger
fact, which the region-level differential harness confirms on dirty memory, is
that the OR-mask the replacement contributes to each limb is *bit-identical* to
the mask the reference accumulates byte by byte -- so the equality holds
against an arbitrary prior word as well, and the clearing hypothesis is a
convenience rather than a requirement. -/
theorem or_zero_left (v : Nat) : 0 ||| v = v := by simp

/-! ## Axiom audit -/

#print axioms limb_eq_window
#print axioms top_limb_eq_prefix
#print axioms window_shift_eq_prefix
#print axioms limb_high_eq_zero
#print axioms top_limb_eq_shifted_window
#print axioms top_limb_lt

end Challenge.Modexp.Submission.Proofs.Bytecode.LoadMath
