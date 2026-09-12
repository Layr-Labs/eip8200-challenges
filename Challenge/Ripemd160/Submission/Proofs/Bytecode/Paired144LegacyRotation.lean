import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144LegacyProduct
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Carry

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144LegacyRotation

open Paired144Core Paired144Nat Paired144LegacyProduct

def rawRotate (a b : BitVec 32) (r s : Nat) : BitVec 256 :=
  rawProduct a b (r - s) (s - r) >>> (38 - min r s)

theorem low_rotate (a b : BitVec 32) (r s : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15) (hs0 : 5 ≤ s) (hs : s ≤ 15) :
    low (rawRotate a b r s) = a.rotateLeft r := by
  apply BitVec.eq_of_toNat_eq
  rw [rawRotate, low_shift_toNat a b (r - s) (s - r) (38 - min r s)
    (by omega) (by omega) (by omega), rotate_toNat a r (by omega) (by omega)]
  have he : 38 - min r s - 6 - (r - s) = 32 - r := by omega
  rw [he]

theorem high_rotate (a b : BitVec 32) (r s : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15) (hs0 : 5 ≤ s) (hs : s ≤ 15) :
    high (rawRotate a b r s) = b.rotateLeft s := by
  apply BitVec.eq_of_toNat_eq
  rw [rawRotate, high_shift_toNat a b (r - s) (s - r) (38 - min r s)
    (by omega) (by omega) (by omega) (by omega), rotate_toNat b s (by omega) (by omega)]
  have he : 38 - min r s - 6 - (s - r) = 32 - s := by omega
  rw [he]

theorem rawRotate_gap (a b : BitVec 32) (r s : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15) (hs0 : 5 ≤ s) (hs : s ≤ 15) :
    (rawRotate a b r s).getLsbD (149 - (38 - min r s)) = false := by
  exact shiftedProduct_gap a b (r - s) (s - r) (38 - min r s) (by omega) (by omega)

theorem normalize_rotate (a b : BitVec 32) (r s : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15) (hs0 : 5 ≤ s) (hs : s ≤ 15) :
    normalize (rawRotate a b r s) = pack (a.rotateLeft r) (b.rotateLeft s) := by
  rw [normalize, low_rotate a b r s hr0 hr hs0 hs, high_rotate a b r s hr0 hr hs0 hs]

/-- Arbitrary scalar E addends are included in the machine identity. The
legacy product's own bit149 separator blocks carry into the high lane. -/
theorem normalize_rotate_add (a b e f : BitVec 32) (r s : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15) (hs0 : 5 ≤ s) (hs : s ≤ 15) :
    normalize (rawRotate a b r s + pack e f) =
      pack (a.rotateLeft r + e) (b.rotateLeft s + f) := by
  rw [Paired144Carry.normalize_add_pack _ e f (149 - (38 - min r s))
    (by omega) (by omega) (rawRotate_gap a b r s hr0 hr hs0 hs),
    low_rotate a b r s hr0 hr hs0 hs, high_rotate a b r s hr0 hr hs0 hs]

theorem normalize_cRotate (a b : BitVec 32) :
    normalize (rawProduct a b 0 0 >>> 28) = pack (a.rotateLeft 10) (b.rotateLeft 10) := by
  exact normalize_rotate a b 10 10 (by decide) (by decide) (by decide) (by decide)

#print axioms low_rotate
#print axioms high_rotate
#print axioms rawRotate_gap
#print axioms normalize_rotate
#print axioms normalize_rotate_add
#print axioms normalize_cRotate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144LegacyRotation
