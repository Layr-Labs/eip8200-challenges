import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFBridge

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000

/-!
# Packed Boolean slot bound

Bitwise Boolean evaluation preserves the 64-bit slot containing its inputs.
This is the missing no-cross-lane-carry premise for the packed round sum.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFSlotBound

open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFBridge

private theorem slot_or_lt (a b n : Nat)
    (ha : a % 2 ^ 64 < 2 ^ n) (hb : b % 2 ^ 64 < 2 ^ n) :
    (a ||| b) % 2 ^ 64 < 2 ^ n := by
  rw [Nat.or_mod_two_pow]
  exact Nat.or_lt_two_pow ha hb

private theorem slot_and_lt (a b n : Nat)
    (hb : b % 2 ^ 64 < 2 ^ n) :
    (a &&& b) % 2 ^ 64 < 2 ^ n := by
  rw [Nat.and_mod_two_pow]
  exact Nat.and_lt_two_pow _ hb

private theorem slot_xor_lt (a b n : Nat)
    (ha : a % 2 ^ 64 < 2 ^ n) (hb : b % 2 ^ 64 < 2 ^ n) :
    (a ^^^ b) % 2 ^ 64 < 2 ^ n := by
  rw [Nat.xor_mod_two_pow]
  exact Nat.xor_lt_two_pow ha hb

private theorem maskL_slot_lt (n : Nat) (hn : 32 ≤ n) :
    maskLN % 2 ^ 64 < 2 ^ n := by
  calc
    maskLN % 2 ^ 64 ≤ maskLN := Nat.mod_le _ _
    _ < 2 ^ 32 := by simp [maskLN]
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

private theorem maskR_slot_lt (n : Nat) : maskRN % 2 ^ 64 < 2 ^ n := by
  simp [maskRN]

private theorem maskLR_slot_lt (n : Nat) (hn : 32 ≤ n) :
    maskLRN % 2 ^ 64 < 2 ^ n := by
  rw [maskLRN_or]
  exact slot_or_lt maskRN maskLN n (maskR_slot_lt n) (maskL_slot_lt n hn)

/-- A packed Boolean function cannot set a bit above the occupied portion of
slot 0.  The `32 ≤ n` premise is exactly what is needed for the low-lane masks.
-/
theorem natPackedF_slot_lt (r x y z n : Nat) (hr : r < 5) (hn : 32 ≤ n)
    (hx : x % 2 ^ 64 < 2 ^ n) (hy : y % 2 ^ 64 < 2 ^ n)
    (hz : z % 2 ^ 64 < 2 ^ n) :
    PackedF.natPackedF r x y z % 2 ^ 64 < 2 ^ n := by
  have hL := maskL_slot_lt n hn
  have hR := maskR_slot_lt n
  have hLR := maskLR_slot_lt n hn
  interval_cases r
  · exact slot_xor_lt _ _ n
      (slot_xor_lt _ _ n (slot_xor_lt x y n hx hy) hR)
      (slot_or_lt _ _ n (slot_and_lt y maskRN n hR) hz)
  · exact slot_xor_lt _ _ n
      (slot_xor_lt _ _ n
        (slot_and_lt (y ^^^ z) x n hx) hz)
      (slot_and_lt _ maskRN n hR)
  · exact slot_xor_lt _ z n
      (slot_or_lt _ x n (slot_xor_lt y maskLRN n hy hLR) hx) hz
  · exact slot_xor_lt _ _ n
      (slot_xor_lt _ y n
        (slot_and_lt (x ^^^ y) z n hz) hy)
      (slot_and_lt _ maskRN n hR)
  · exact slot_xor_lt _ _ n
      (slot_xor_lt _ maskLN n (slot_xor_lt x y n hx hy) hL)
      (slot_or_lt _ z n (slot_and_lt y maskLN n hL) hz)

/-- The exact carry bound required by the packed step: inter-step `b` and `c`
may have one carry bit, while freshly masked `d` is clean. -/
theorem packedFWord_slot0_lt33 (r : Nat) (b c d : EvmSemantics.UInt256)
    (hr : r < 5) (hb : Inv b) (hc : Inv c) (hd : Clean d) :
    (packedFWord r b c d).toNat % 2 ^ 64 < 2 ^ 33 := by
  rw [packedFWord_toNat r b c d hr]
  exact natPackedF_slot_lt r b.toNat c.toNat d.toNat 33 hr (by omega)
    hb.low hc.low
      (lt_of_lt_of_le hd.low (by norm_num : 2 ^ (32 : Nat) ≤ 2 ^ 33))

#print axioms natPackedF_slot_lt
#print axioms packedFWord_slot0_lt33

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFSlotBound
