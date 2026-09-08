import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.Ring

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# The packed rotation: doubling by `2^32 + 1`, and the two lane windows

This module holds the rotation half of the packed-lane development.  The mask
decomposition (`and_maskLR_split`) and the step-boundary invariant (`Clean`,
`Inv`, `masked_word_split`, `inv_of_rot_add`) are **imported**, not restated:
`Clean` and `Inv` are declared exactly once in the tree, in
`PackedLaneInvariant`, and every fact here is stated over those definitions.

The mechanism, read off the generator (`build_packed_nomcopy_v2.py`,
`emit_steps`): a rotate is

    AND maskLR ; MUL c ; SHR (32 - r) ; AND laneMask        with c = 2^32 + 1

`MUL c` doubles each 32-bit lane into an exact 64-bit block.  Because the lanes
sit 64 apart and each is strictly below `2^32`, the two doubled blocks occupy
`[0,64)` and `[64,128)` and **abut without overlapping** — that non-overlap is
the entire reason lane 1 is at bit 64 rather than bit 128, and it is what
`window_packed_lane0` / `window_packed_lane1` prove.

## On the multiply premise

The premise carried into the multiplication is `masked_word_split`, the
**whole-word** identity

    (P &&& maskLR).toNat = lane0N P.toNat + lane1N P.toNat * 2 ^ 64

and NOT a pair of `windowN _ _ < 2 ^ 32` bounds.  Those bounds hold for any
word by construction — extracting a 32-bit window always yields something below
`2 ^ 32` — so they are a tautology and constrain nothing.  What has to be
excluded is gap junk in bits 32..63 (and junk above bit 95) reaching into the
other lane's region under `MUL c`, and only the equation says that.

## Which hypotheses are load-bearing

Measured, by searching for violating inputs rather than by inspection:

* `window_packed_lane0`, `hk : k ≤ 32` — REQUIRED.  At `k = 40`, 3980/4000
  random `(L,R)` violate the conclusion.
* `window_packed_lane1`, `hL : L < 2 ^ 32` — REQUIRED.  With `L ≥ 2^32` at
  `k = 0`, 3000/3000 violate it: the low block's carry is read as lane 1.
  This is precisely the abutting-blocks fact.
* `window_packed_lane1`, `hR` and `hk` — NOT load-bearing (0 violations at
  `k = 0,22,40,64,100` and for `R` up to `2^200`).  They are kept in the
  signature for uniformity with lane 0 and are named `_hR` / `_hk` so the
  unused-variable linter does not fire under `warningAsError`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot

open EvmSemantics
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant

/-! ## 0.  Local word primitives

`Challenge.EvmProof.Word` has no multiplication lemma at all, and the two
copies inside the Ripemd160 tree (`RotationMultiply.lean:41`,
`RotationParameter.lean:60`) are both `private`, so none is citable here.
This is the same statement and the same proof, re-declared privately. -/

private theorem mul_toNat (a b : UInt256) :
    (UInt256.mul a b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

/-! ## 1.  The rotation multiplier -/

/-- The doubling constant `2^32 + 1`: one `MUL` places a copy of each lane 32
bits above itself, so a single `SHR` can read any rotation of it. -/
def cN : Nat := 2 ^ 32 + 1

def cMul : UInt256 := UInt256.ofNat cN

private theorem cN_lt : cN < 2 ^ 256 := by
  unfold cN
  norm_num

@[simp] theorem cMul_toNat : cMul.toNat = cN := by
  rw [cMul, word_toNat_ofNat]
  exact Nat.mod_eq_of_lt cN_lt

/-! ## 2.  Windows compose with shifts

`windowN` is imported from `PackedLaneMask`; these three say how it interacts
with `>>>`, which the mask module did not need. -/

theorem windowN_shiftRight (p k j : Nat) :
    windowN (p >>> j) k = windowN p (j + k) := by
  simp only [windowN, Nat.shiftRight_add]

theorem lane0N_shiftRight (p j : Nat) : lane0N (p >>> j) = windowN p j := by
  simp only [lane0N, windowN_shiftRight, Nat.add_zero]

theorem lane1N_shiftRight (p j : Nat) :
    lane1N (p >>> j) = windowN p (j + 64) := by
  simp only [lane1N, windowN_shiftRight]

/-! ## 3.  Where a window can and cannot see

Two structural facts about a value presented as `A + B * 2 ^ 64`. -/

/-- A window at offset `k ≤ 32` cannot reach bit 64: whatever sits above the
low block contributes a multiple of `2 ^ 32` after the shift and vanishes.
`hk` is load-bearing — see the module docstring. -/
theorem windowN_add_high (A B k : Nat) (hk : k ≤ 32) :
    windowN (A + B * 2 ^ 64) k = windowN A k := by
  have hpos : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
  have hcollect : (2 : Nat) ^ (32 - k) * 2 ^ 32 * 2 ^ k = 2 ^ 64 := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have hsplit : A + B * 2 ^ 64 = A + B * 2 ^ (32 - k) * 2 ^ 32 * 2 ^ k := by
    calc A + B * 2 ^ 64
        = A + B * (2 ^ (32 - k) * 2 ^ 32 * 2 ^ k) := by rw [hcollect]
      _ = A + B * 2 ^ (32 - k) * 2 ^ 32 * 2 ^ k := by ring
  simp only [windowN]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hsplit,
    Nat.add_mul_div_right _ _ hpos, Nat.add_mul_mod_self_right]

/-- Above bit 63 the low block is invisible — provided it really is a low
block.  `hA : A < 2 ^ 64` is exactly the abutting-blocks hypothesis and is
load-bearing; without it the low block's carry is read as lane 1. -/
theorem windowN_add_low (A B k : Nat) (hA : A < 2 ^ 64) :
    windowN (A + B * 2 ^ 64) (k + 64) = windowN B k := by
  have hpos : 0 < (2 : Nat) ^ 64 := Nat.two_pow_pos 64
  have hdiv64 : (A + B * 2 ^ 64) / 2 ^ 64 = B := by
    rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hA, Nat.zero_add]
  have hpow : (2 : Nat) ^ (k + 64) = 2 ^ 64 * 2 ^ k := by
    rw [← Nat.pow_add]
    congr 1
    omega
  simp only [windowN]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hpow,
    ← Nat.div_div_eq_div_mul, hdiv64]

/-! ## 4.  The abutting-blocks fact -/

/-- One lane doubles into an exact 64-bit block.  This deliberately violates
`Inv`: `x * c = x * 2^32 + x` occupies bits 0..63, which is the transient, and
it must NOT be folded into the step invariant.  It lives here, between the mask
and the shift, with its own pre- and post-condition. -/
theorem doubled_lt (x : Nat) (hx : x < 2 ^ 32) : cN * x < 2 ^ 64 := by
  have hxle : x ≤ 2 ^ 32 - 1 := by omega
  have hle : cN * x ≤ cN * (2 ^ 32 - 1) := Nat.mul_le_mul (Nat.le_refl _) hxle
  have hval : cN * (2 ^ 32 - 1) = 2 ^ 64 - 1 := by
    unfold cN
    norm_num
  have hlast : (2 : Nat) ^ 64 - 1 < 2 ^ 64 := by norm_num
  rw [hval] at hle
  exact Nat.lt_of_le_of_lt hle hlast

/-- **The abutting-blocks fact.**  With the lanes 64 apart and each strictly
below `2 ^ 32`, the two doubled blocks occupy `[0,64)` and `[64,128)` and do not
overlap, so the product splits slotwise. -/
theorem packed_mul_split (L R : Nat) (hL : L < 2 ^ 32) (_hR : R < 2 ^ 32) :
    cN * (L + R * 2 ^ 64) = cN * L + (cN * R) * 2 ^ 64 ∧
      (cN * (L + R * 2 ^ 64)) % 2 ^ 64 = cN * L ∧
      (cN * (L + R * 2 ^ 64)) / 2 ^ 64 = cN * R := by
  have hsplit : cN * (L + R * 2 ^ 64) = cN * L + (cN * R) * 2 ^ 64 := by ring
  have hlow : cN * L < 2 ^ 64 := doubled_lt L hL
  refine ⟨hsplit, ?_, ?_⟩
  · rw [hsplit, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hlow
  · rw [hsplit, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64),
      Nat.div_eq_of_lt hlow, Nat.zero_add]

/-- **The MUL no-wrap fact.**  The doubled product of a two-lane word stays
inside a 256-bit word, so the EVM `MUL` does not truncate. -/
theorem packed_mul_lt (L R : Nat) (hL : L < 2 ^ 32) (hR : R < 2 ^ 32) :
    cN * (L + R * 2 ^ 64) < 2 ^ 256 := by
  have hsplit := (packed_mul_split L R hL hR).1
  have hl : cN * L < 2 ^ 64 := doubled_lt L hL
  have hr : cN * R < 2 ^ 64 := doubled_lt R hR
  have hrle : cN * R ≤ 2 ^ 64 - 1 := by omega
  have hb : (cN * R) * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 :=
    Nat.mul_le_mul hrle (Nat.le_refl _)
  have hnum : (2 ^ 64 - 1) * 2 ^ 64 + 2 ^ 64 < 2 ^ 256 := by norm_num
  rw [hsplit]
  omega

/-- **The MUL wrapper.**  `toNat` of the EVM multiplication of `cMul` against a
`maskLR`-masked word is the honest `Nat` product.

The premise is `masked_word_split` — the whole-word identity — not a pair of
window bounds.  That is what rules out gap junk being doubled into the other
lane's region. -/
theorem mul_cMul_toNat (P : UInt256) :
    (UInt256.mul cMul (P &&& maskLR)).toNat
      = cN * (lane0N P.toNat + lane1N P.toNat * 2 ^ 64) := by
  have hlt : cN * (lane0N P.toNat + lane1N P.toNat * 2 ^ 64) < 2 ^ 256 :=
    packed_mul_lt _ _ (windowN_lt _ _) (windowN_lt _ _)
  rw [mul_toNat, cMul_toNat, masked_word_split P]
  exact Nat.mod_eq_of_lt hlt

/-! ## 5.  The doubled block, read at an offset, is a rotation -/

/-- The 32-bit window of a doubled block at offset `32 - r` is the left
rotation of the lane by `r`.  This is `RotationFold.rawRot_or_fold`'s content
transposed from the word level to `Nat`, where both lanes can instantiate it. -/
theorem window_doubled (x r : Nat) (hx : x < 2 ^ 32)
    (hr0 : 0 < r) (hr : r < 32) :
    windowN (cN * x) (32 - r) = (x <<< r ||| x >>> (32 - r)) % 2 ^ 32 := by
  have _hr0 := hr0
  have hpos : 0 < (2 : Nat) ^ (32 - r) := Nat.two_pow_pos _
  have hpow : (2 : Nat) ^ r * 2 ^ (32 - r) = 2 ^ 32 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  -- the low half of the rotation fits under the high half, so the OR is a sum
  have hlow : x >>> (32 - r) < 2 ^ r := by
    rw [Nat.shiftRight_eq_div_pow]
    refine (Nat.div_lt_iff_lt_mul hpos).mpr ?_
    rw [hpow]
    exact hx
  have hor : x <<< r ||| x >>> (32 - r) = x * 2 ^ r + x / 2 ^ (32 - r) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hlow x, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
  -- and the doubled block, shifted, is the same sum
  have hsplit : cN * x = x + x * 2 ^ r * 2 ^ (32 - r) := by
    have hx32 : x * (2 ^ r * 2 ^ (32 - r)) = x * 2 ^ 32 := by rw [hpow]
    unfold cN
    calc (2 ^ 32 + 1) * x = x + x * 2 ^ 32 := by ring
      _ = x + x * (2 ^ r * 2 ^ (32 - r)) := by rw [hx32]
      _ = x + x * 2 ^ r * 2 ^ (32 - r) := by ring
  simp only [windowN]
  rw [Nat.shiftRight_eq_div_pow, hsplit, Nat.add_mul_div_right _ _ hpos, hor,
    Nat.add_comm (x / 2 ^ (32 - r)) (x * 2 ^ r)]

/-! ## 6.  The two lane projections of the shifted product

This is the non-overlap payoff: after `MUL c ; SHR k` with `k ≤ 32`, lane 0
reads lane 0's doubled block and lane 1 reads lane 1's, with no crosstalk. -/

/-- Lane 0 of `SHR k` applied to the packed product reads lane 0's doubled
block. -/
theorem window_packed_lane0 (L R k : Nat)
    (hL : L < 2 ^ 32) (hR : R < 2 ^ 32) (hk : k ≤ 32) :
    lane0N ((cN * (L + R * 2 ^ 64)) >>> k) = windowN (cN * L) k := by
  rw [lane0N_shiftRight, (packed_mul_split L R hL hR).1]
  exact windowN_add_high (cN * L) (cN * R) k hk

/-- Lane 1 of `SHR k` applied to the packed product reads lane 1's doubled
block.  `hL` is what makes this true: it is the statement that lane 0's doubled
block stops at bit 63.  `_hR` and `_hk` are not load-bearing here. -/
theorem window_packed_lane1 (L R k : Nat)
    (hL : L < 2 ^ 32) (_hR : R < 2 ^ 32) (_hk : k ≤ 32) :
    lane1N ((cN * (L + R * 2 ^ 64)) >>> k) = windowN (cN * R) k := by
  rw [lane1N_shiftRight, (packed_mul_split L R hL _hR).1]
  exact windowN_add_low (cN * L) (cN * R) k (doubled_lt L hL)

/-! ## 7.  `rol10`

`32 - 10 = 22`, so `rol10` is the same extraction at a fixed shift.  The
trailing `AND maskLR` is what makes the result `Clean` rather than merely
`Inv`, which is the design choice that lets the post-add truncation mask be
dropped. -/

def packedRol10 (C : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul cMul (C &&& maskLR)) (UInt256.ofNat 22)
    &&& maskLR

/-- `rol10`'s output is `Clean`, from the imported invariant module. -/
theorem packedRol10_clean (C : UInt256) : Clean (packedRol10 C) :=
  masked_input_clean _

private theorem packedRol10_pre_toNat (C : UInt256) :
    (UInt256.shiftRight (UInt256.mul cMul (C &&& maskLR))
      (UInt256.ofNat 22)).toNat
      = (cN * (lane0N C.toNat + lane1N C.toNat * 2 ^ 64)) >>> 22 := by
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by norm_num : (22 : Nat) < 256),
    mul_cMul_toNat]

private theorem sub_ten : (32 : Nat) - 10 = 22 := by norm_num

/-- **`rol10` acts as a left-rotation by 10 in both lanes, independently.**
Stated on `Nat` lanes, which is what the packed step development consumes; the
`UInt32`/`Crypto.Ripemd160.rotl32` restatement is a separate bridge and is
deliberately not part of this module. -/
theorem packedRol10_lanes (C : UInt256) :
    lane0N (packedRol10 C).toNat
        = (lane0N C.toNat <<< 10 ||| lane0N C.toNat >>> 22) % 2 ^ 32 ∧
      lane1N (packedRol10 C).toNat
        = (lane1N C.toNat <<< 10 ||| lane1N C.toNat >>> 22) % 2 ^ 32 := by
  have hL : lane0N C.toNat < 2 ^ 32 := windowN_lt _ _
  have hR : lane1N C.toNat < 2 ^ 32 := windowN_lt _ _
  have hk : (22 : Nat) ≤ 32 := by norm_num
  have hrot0 := window_doubled (lane0N C.toNat) 10 hL (by norm_num) (by norm_num)
  have hrot1 := window_doubled (lane1N C.toNat) 10 hR (by norm_num) (by norm_num)
  rw [sub_ten] at hrot0 hrot1
  constructor
  · rw [packedRol10, lane0_and_maskLR, packedRol10_pre_toNat,
      window_packed_lane0 _ _ 22 hL hR hk]
    exact hrot0
  · rw [packedRol10, lane1_and_maskLR, packedRol10_pre_toNat,
      window_packed_lane1 _ _ 22 hL hR hk]
    exact hrot1

#print axioms windowN_add_high
#print axioms windowN_add_low
#print axioms doubled_lt
#print axioms packed_mul_split
#print axioms packed_mul_lt
#print axioms mul_cMul_toNat
#print axioms window_doubled
#print axioms window_packed_lane0
#print axioms window_packed_lane1
#print axioms packedRol10_clean
#print axioms packedRol10_lanes

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot
