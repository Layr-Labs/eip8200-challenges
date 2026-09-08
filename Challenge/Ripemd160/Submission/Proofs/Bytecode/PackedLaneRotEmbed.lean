import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# `rol10` against the pinned `Crypto.Ripemd160.rotl32`

An ADDENDUM to `PackedLaneRot`, which is frozen and proved (801/801, axioms
`[propext, Classical.choice, Quot.sound]`).  This module adds nothing to that
file and changes nothing in it; it only restates the already-proved
`packedRol10_lanes` in the lane-indexed `UInt32.ofNat` shape that
`PackedFBridge`'s `packedFWord_lane0_ripemdF` / `packedFWord_lane1_ripemdF`
use, so the rotate side and the `f` side compose in the step lemma without a
further adapter between two conventions of our own.

## Why this is not a one-liner

Nothing in the tree computes `.toNat` of a `rotl32`.  Every existing `rotl32`
lemma — `EvmProof.Word.evm_rotl32`, `Bytecode.Word.evmRotl32_ofUInt32`,
`StackRound.stackRawRot_embed` — is stated at the `UInt256` / `ofUInt32` /
`mask32` level and never descends to `Nat`.  So the bridge is built from the
core `UInt32` lemmas, and two things there are awkward:

* `UInt32.shiftLeft` / `UInt32.shiftRight` reduce the shift amount **mod 32**
  (`Init/Data/UInt/Basic.lean:491,498`), so the `toNat` lemmas emit
  `b.toNat % 32`;
* `UInt32.toNat_ofNat'` fires *before* that reduction, so the shift amount
  arrives as the nested `r % 2 ^ 32 % 32` and needs two `Nat.mod_eq_of_lt`
  steps to collapse.

That is the same shape as `PackedOutputMath.uint32_byte`, which is the in-tree
template this follows.

STATUS: WRITTEN, NOT ELABORATED.  Zero `sorry`.  Nothing here is proved until
it elaborates and `#print axioms` is clean.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRotEmbed

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRot

/-- The raw two-shift-and-OR `Nat` expression is exactly `toNat` of the pinned
`Crypto.Ripemd160.rotl32`, for any in-range lane value and any `0 < r < 32`.

Stated for general `r` rather than only `r = 10`: the 80-step body uses ten
distinct rotation amounts, and this is the lemma each of them instantiates.

`hr0` IS load-bearing here (unlike in `window_doubled`, where it is not): it is
what gives `32 - r < 32`, without which the mod-32 reduction of the `UInt32`
shift does not collapse. -/
theorem rotl32_ofNat_toNat (L r : Nat) (hL : L < 2 ^ 32)
    (hr0 : 0 < r) (hr : r < 32) :
    (Crypto.Ripemd160.rotl32 (UInt32.ofNat L) r).toNat
      = (L <<< r ||| L >>> (32 - r)) % 2 ^ 32 := by
  have hLmod : L % 2 ^ 32 = L := Nat.mod_eq_of_lt hL
  have hrmod : r % 2 ^ 32 % 32 = r := by
    rw [Nat.mod_eq_of_lt (show r < 2 ^ 32 by omega), Nat.mod_eq_of_lt hr]
  have hsmod : (32 - r) % 2 ^ 32 % 32 = 32 - r := by
    rw [Nat.mod_eq_of_lt (show 32 - r < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show 32 - r < 32 by omega)]
  have hhigh : L >>> (32 - r) % 2 ^ 32 = L >>> (32 - r) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le L (32 - r)) hL)
  show ((UInt32.ofNat L <<< UInt32.ofNat r) |||
      (UInt32.ofNat L >>> UInt32.ofNat (32 - r))).toNat = _
  rw [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight,
    UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
    hLmod, hrmod, hsmod, Nat.or_mod_two_pow, hhigh]

private theorem sub_ten : (32 : Nat) - 10 = 22 := by norm_num

/-- Lane 0 of `rol10` is the pinned `rotl32 _ 10` of lane 0.  Shaped to pair
with `PackedFBridge.packedFWord_lane0_ripemdF`. -/
theorem packedRol10_lane0_ripemdRot (C : UInt256) :
    lane0N (packedRol10 C).toNat
      = (Crypto.Ripemd160.rotl32
          (UInt32.ofNat (lane0N C.toNat)) 10).toNat := by
  have hL : lane0N C.toNat < 2 ^ 32 := windowN_lt _ _
  have e0 := rotl32_ofNat_toNat (lane0N C.toNat) 10 hL (by norm_num) (by norm_num)
  rw [sub_ten] at e0
  exact (packedRol10_lanes C).1.trans e0.symm

/-- Lane 1 of `rol10` is the pinned `rotl32 _ 10` of lane 1.  Shaped to pair
with `PackedFBridge.packedFWord_lane1_ripemdF`. -/
theorem packedRol10_lane1_ripemdRot (C : UInt256) :
    lane1N (packedRol10 C).toNat
      = (Crypto.Ripemd160.rotl32
          (UInt32.ofNat (lane1N C.toNat)) 10).toNat := by
  have hR : lane1N C.toNat < 2 ^ 32 := windowN_lt _ _
  have e1 := rotl32_ofNat_toNat (lane1N C.toNat) 10 hR (by norm_num) (by norm_num)
  rw [sub_ten] at e1
  exact (packedRol10_lanes C).2.trans e1.symm

#print axioms rotl32_ofNat_toNat
#print axioms packedRol10_lane0_ripemdRot
#print axioms packedRol10_lane1_ripemdRot

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneRotEmbed
