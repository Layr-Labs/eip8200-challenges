import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13PoolRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableMemory

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# The pool load, split into its two lanes and its two junk fields

A pool load is a 32-byte window whose last four bytes are the schedule field, whose bytes
`10..13` are the same field again (the fan duplicates every field eighteen bytes apart), and
whose other twenty-four bytes are whatever the previous table image left there.  Writing the
window big-endian,

    rawLoad memory i  =  jr * 2^176  +  hiLane * 2^144  +  jl * 2^32  +  loLane

which is exactly `UInt256.mul coefficient w + StaggerRound.junk jl jr` when both lanes hold the
same `w`.  The mask `poolMask` keeps only the two lanes; the eight JD8 sites no longer apply it,
so `jl` and `jr` reach the table.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Pool
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Pair13PoolRaw

/-- Bytes `a+28 .. a+31`: the schedule field itself. -/
def loLane (memory : ByteArray) (i : Nat) : Nat :=
  Precompile.bytesToNatPadded memory (poolAddr i + 28) 4

/-- Bytes `a+14 .. a+27`: the junk the lower lane carries into bits 32..143. -/
def jlOf (memory : ByteArray) (i : Nat) : Nat :=
  Precompile.bytesToNatPadded memory (poolAddr i + 14) 14

/-- Bytes `a+10 .. a+13`: the fan's duplicate of the schedule field. -/
def hiLane (memory : ByteArray) (i : Nat) : Nat :=
  Precompile.bytesToNatPadded memory (poolAddr i + 10) 4

/-- Bytes `a .. a+9`: the junk above the upper lane, bits 176..255. -/
def jrOf (memory : ByteArray) (i : Nat) : Nat :=
  Precompile.bytesToNatPadded memory (poolAddr i) 10

theorem loLane_lt (memory : ByteArray) (i : Nat) : loLane memory i < 2 ^ 32 := by
  have h := Bytes.bytesToNatPadded_lt_pow memory (poolAddr i + 28) 4
  simpa only [loLane, show (256 : Nat) ^ 4 = 2 ^ 32 by norm_num] using h

theorem hiLane_lt (memory : ByteArray) (i : Nat) : hiLane memory i < 2 ^ 32 := by
  have h := Bytes.bytesToNatPadded_lt_pow memory (poolAddr i + 10) 4
  simpa only [hiLane, show (256 : Nat) ^ 4 = 2 ^ 32 by norm_num] using h

theorem jlOf_lt (memory : ByteArray) (i : Nat) : jlOf memory i < 2 ^ 112 := by
  have h := Bytes.bytesToNatPadded_lt_pow memory (poolAddr i + 14) 14
  simpa only [jlOf, show (256 : Nat) ^ 14 = 2 ^ 112 by norm_num] using h

theorem jrOf_lt (memory : ByteArray) (i : Nat) : jrOf memory i < 2 ^ 80 := by
  have h := Bytes.bytesToNatPadded_lt_pow memory (poolAddr i) 10
  simpa only [jrOf, show (256 : Nat) ^ 10 = 2 ^ 80 by norm_num] using h

/-- The big-endian split of a pool load into its four fields. -/
theorem rawLoad_split (memory : ByteArray) (i : Nat) :
    (rawLoad memory i).toNat
      = loLane memory i + jlOf memory i * 2 ^ 32
        + hiLane memory i * 2 ^ 144 + jrOf memory i * 2 ^ 176 := by
  have h1 := Bytes.bytesToNatPadded_add memory (poolAddr i) 28 4
  have h2 := Bytes.bytesToNatPadded_add memory (poolAddr i) 14 14
  have h3 := Bytes.bytesToNatPadded_add memory (poolAddr i) 10 4
  rw [show (28 : Nat) + 4 = 32 from rfl] at h1
  rw [show (14 : Nat) + 14 = 28 from rfl] at h2
  rw [show (10 : Nat) + 4 = 14 from rfl] at h3
  rw [rawLoad, Bytes.readWord_toNat, h1, h2, h3]
  simp only [loLane, jlOf, hiLane, jrOf,
    show (256 : Nat) ^ 4 = 2 ^ 32 by norm_num,
    show (256 : Nat) ^ 14 = 2 ^ 112 by norm_num]
  ring

/-- The surviving half of a raw slot store: the field plus its fourteen junk bytes. -/
theorem raw_lo (memory : ByteArray) (i : Nat) (h : poolWord memory i = rawLoad memory i) :
    (poolWord memory i).toNat % 2 ^ 144 = loLane memory i + jlOf memory i * 2 ^ 32 := by
  rw [h, rawLoad_split]
  have hl := loLane_lt memory i
  have hj := jlOf_lt memory i
  have hb : loLane memory i + jlOf memory i * 2 ^ 32 < 2 ^ 144 := by
    have : jlOf memory i * 2 ^ 32 ≤ (2 ^ 112 - 1) * 2 ^ 32 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  omega

/-- The half an ELIDED slot receives: the fan's duplicate of the field, plus the ten junk
bytes above it. -/
theorem raw_hi (memory : ByteArray) (i : Nat) (h : poolWord memory i = rawLoad memory i) :
    (poolWord memory i).toNat / 2 ^ 144 = hiLane memory i + jrOf memory i * 2 ^ 32 := by
  rw [h, rawLoad_split]
  have hl := loLane_lt memory i
  have hj := jlOf_lt memory i
  have hb : loLane memory i + jlOf memory i * 2 ^ 32 < 2 ^ 144 := by
    have : jlOf memory i * 2 ^ 32 ≤ (2 ^ 112 - 1) * 2 ^ 32 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  omega

/-- **The junk bound.**  A fourteen-byte window carrying a zero two-byte window anywhere inside
it stays at least 65,535 below `2 ^ 112`, hence below the carry threshold `2 ^ 112 - 4` that
`normalize` needs.  Each of the eight unmasked words has such a pair, at `p` equal to 0, 4, 8
or 12 depending on where its junk window crosses a fan gap.

This is the shape the obligation actually has.  The mask is NOT an identity on the loaded value
-- it clears bits on almost every execution -- so nothing here claims the discarded bits are
absent.  It claims they are small enough that the round's `normalize` cannot see them. -/
theorem window_bound (m : ByteArray) (A p : Nat) (hp : p ≤ 12)
    (hz : Precompile.bytesToNatPadded m (A + p) 2 = 0) :
    Precompile.bytesToNatPadded m A 14 < 2 ^ 112 - 4 := by
  have hs1 := Bytes.bytesToNatPadded_add m A p (14 - p)
  rw [show p + (14 - p) = 14 by omega] at hs1
  have hs2 := Bytes.bytesToNatPadded_add m (A + p) 2 (12 - p)
  rw [show 2 + (12 - p) = 14 - p by omega, hz, Nat.zero_mul, Nat.zero_add] at hs2
  have hA := Bytes.bytesToNatPadded_lt_pow m A p
  have hB := Bytes.bytesToNatPadded_lt_pow m (A + p + 2) (12 - p)
  rw [hs1, hs2]
  interval_cases p <;> norm_num at hA hB ⊢ <;> omega

/-- The junk of a raw load, bounded below the carry threshold by a zero two-byte window. -/
theorem jlOf_bound (m : ByteArray) (i p : Nat) (hp : p ≤ 12)
    (hz : Precompile.bytesToNatPadded m (poolAddr i + 14 + p) 2 = 0) :
    jlOf m i < 2 ^ 112 - 4 :=
  window_bound m (poolAddr i + 14) p hp hz

/-- The byte-to-window bridge: two zero bytes make a zero two-byte window. -/
theorem window2_of_bytes (m : ByteArray) (x : Nat)
    (h0 : m[x]?.getD 0 = 0) (h1 : m[x + 1]?.getD 0 = 0) :
    Precompile.bytesToNatPadded m x 2 = 0 := by
  have hb : ∀ y : Nat, m[y]?.getD 0 = 0 →
      (YulSemantics.EVM.byteFrom m.toList y).toNat = 0 := by
    intro y hy
    have hy' : YulSemantics.EVM.byteFrom m.toList y = m[y]?.getD 0 := by
      unfold YulSemantics.EVM.byteFrom
      rw [YulEvmCompiler.ByteArray.toList_eq_data, List.getD_eq_getElem?_getD,
        Array.getElem?_toList]
      rfl
    rw [hy', hy]
    rfl
  have e2 := Bytes.bytesToNatPadded_succ m x 1
  have e1 := Bytes.bytesToNatPadded_succ m x 0
  have e0 := Bytes.bytesToNatPadded_zero_width m x
  rw [show (1 : Nat) + 1 = 2 from rfl] at e2
  rw [show (0 : Nat) + 1 = 1 from rfl, Nat.add_zero, e0, Nat.zero_mul, Nat.zero_add,
    hb x h0] at e1
  rw [e2, e1, hb (x + 1) h1]

/-! ## Word 3, whose broadcast the artifact rebuilds with `DUP1; SHL 144; OR` -/

theorem lor_div_two_pow (a b n : Nat) : (a ||| b) / 2 ^ n = a / 2 ^ n ||| b / 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_div_two_pow, Nat.testBit_or]

theorem lor_mod_two_pow (a b n : Nat) : (a ||| b) % 2 ^ n = a % 2 ^ n ||| b % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or]
  cases Nat.lt_or_ge i n with
  | inl h => simp only [decide_eq_true h, Bool.true_and]
  | inr h => simp only [decide_eq_false (by omega : ¬ i < n), Bool.false_and, Bool.or_self]

theorem shl144_toNat (v : UInt256) :
    (UInt256.shiftLeft v (UInt256.ofNat 144)).toNat = v.toNat % 2 ^ 112 * 2 ^ 144 := by
  have hs : (UInt256.ofNat 144 : UInt256).toNat = 144 := by
    rw [Word.word_toNat_ofNat]; norm_num
  have hsz : UInt256.size = 2 ^ 112 * 2 ^ 144 := by
    rw [← Nat.pow_add]; rfl
  have hlt : v.toNat % 2 ^ 112 * 2 ^ 144 < 2 ^ 112 * 2 ^ 144 :=
    (Nat.mul_lt_mul_right (Nat.two_pow_pos 144)).mpr (Nat.mod_lt _ (Nat.two_pow_pos 112))
  unfold UInt256.shiftLeft
  rw [hs, if_neg (by omega), Word.word_toNat_ofNat, Nat.shiftLeft_eq, hsz,
    Nat.mul_mod_mul_right]
  have h256 : (2:Nat) ^ 256 = 2 ^ 112 * 2 ^ 144 := by rw [← Nat.pow_add]
  exact Nat.mod_eq_of_lt (by rw [h256]; exact hlt)

/-- Word 3's upper lane sits in the zero prefix, so the rebuilt broadcast still carries the
field itself in the low 32 bits of its HIGH half -- which is what an elided slot receives. -/
theorem three_hi_low32 (memory : ByteArray) (hz : hiLane memory 3 = 0) :
    (poolWord memory 3).toNat / 2 ^ 144 % 2 ^ 32 = loLane memory 3 := by
  have hsplit := rawLoad_split memory 3
  have hl := loLane_lt memory 3
  have hj := jlOf_lt memory 3
  rw [poolWord_three_raw, Word.word_toNat_lor, shl144_toNat, lor_div_two_pow, lor_mod_two_pow]
  have h1 : (rawLoad memory 3).toNat % 2 ^ 112 * 2 ^ 144 / 2 ^ 144 % 2 ^ 32
      = loLane memory 3 := by
    rw [Nat.mul_div_cancel _ (Nat.two_pow_pos 144)]
    rw [hsplit, hz]
    have : jlOf memory 3 * 2 ^ 32 ≤ (2 ^ 112 - 1) * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
    omega
  have h2 : (rawLoad memory 3).toNat / 2 ^ 144 % 2 ^ 32 = 0 := by
    rw [hsplit, hz]
    have : jlOf memory 3 * 2 ^ 32 ≤ (2 ^ 112 - 1) * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
    omega
  rw [h1, h2, Nat.or_zero]

theorem hi144_lt_gen (x : UInt256) : x.toNat / 2 ^ 144 < 2 ^ 112 :=
  Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact x.val.isLt)

#print axioms rawLoad_split
#print axioms raw_lo
#print axioms raw_hi
#print axioms window_bound
#print axioms three_hi_low32
end Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Pool
