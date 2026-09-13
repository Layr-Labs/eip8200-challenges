import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge
import Mathlib.Tactic

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedMultiplierRescale

open EvmSemantics PairedLaneUInt256Bridge

/-- Only the low 176 bits are observed by the paired-word mask. -/
theorem masked_eq_of_low_eq (a b : BitVec 256) (mask : BitVec 176)
    (h : a.setWidth 176 = b.setWidth 176) :
    mask.setWidth 256 &&& a = mask.setWidth 256 &&& b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi256
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth]
  by_cases hi : i < 176
  · have he := congrArg (fun z : BitVec 176 => z.getLsbD i) h
    have hab : a.getLsbD i = b.getLsbD i := by
      simpa only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and] using he
    rw [hab]
  · have hz : mask.getLsbD i = false := BitVec.getLsbD_of_ge mask i (by omega)
    simp only [hz, Bool.and_false, Bool.false_and]

/-- A discarded high product bit cannot reach the low 176 bits after these shifts. -/
theorem low_shift_cancel (z : BitVec 256) (s : Nat)
    (hs : 0 < s) (hbound : s + 176 ≤ 256) :
    ((z <<< 1) >>> s).setWidth 176 = (z >>> (s - 1)).setWidth 176 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi176
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  by_cases hi : i < 176
  · have htop : s + i < 256 := by omega
    have hlow : ¬s + i < 1 := by omega
    have hadd : s + i - 1 = s - 1 + i := by omega
    simp only [hi, decide_true, Bool.true_and, htop, hlow, decide_false,
      Bool.not_false, hadd]
  · simp only [hi, decide_false, Bool.false_and]

/-- The arbitrary addend remains before the mask; no cleanliness hypothesis is needed. -/
theorem bitvec_rescale (x y factor : BitVec 256) (mask : BitVec 176) (s : Nat)
    (hs : 0 < s) (hbound : s + 176 ≤ 256) :
    mask.setWidth 256 &&& (y + (((factor * 2#256) * x) >>> s)) =
      mask.setWidth 256 &&& (y + ((factor * x) >>> (s - 1))) := by
  have hp : (factor * 2#256) * x = (factor * x) <<< 1 := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change (factor * 2#256) * x = (factor * x) * 2#256
    rw [BitVec.mul_assoc, BitVec.mul_assoc, BitVec.mul_comm (2#256) x]
  rw [hp]
  apply masked_eq_of_low_eq
  rw [BitVec.setWidth_add _ _ (by decide), BitVec.setWidth_add _ _ (by decide)]
  rw [low_shift_cancel _ _ hs hbound]

def pairMask : Nat := 95780971281817308448866066055358605703522837925462015

/-- Generic UInt256 form matching PUSH/MUL/PUSH/SHR/DUP/ADD/DUP/AND. -/
theorem rescale (x y : UInt256) (factor s : Nat)
    (hs : 0 < s) (hbound : s + 176 ≤ 256) :
    UInt256.land (UInt256.ofNat pairMask)
      (UInt256.add y (UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat (factor * 2)) x) (UInt256.ofNat s))) =
    UInt256.land (UInt256.ofNat pairMask)
      (UInt256.add y (UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat factor) x) (UInt256.ofNat (s - 1)))) := by
  apply bits_injective
  simp only [bits_land, bits_add, bits_shr _ _ (by omega : s < 256),
    bits_shr _ _ (by omega : s - 1 < 256), bits_mul, bits_ofNat, BitVec.ofNat_mul]
  have hm : BitVec.ofNat 256 pairMask = (BitVec.ofNat 176 pairMask).setWidth 256 := by decide
  rw [hm]
  exact bitvec_rescale (bits x) (bits y) (BitVec.ofNat 256 factor)
    (BitVec.ofNat 176 pairMask) s hs hbound

/-- Exact multiplier and shift at the site recorded as PC1932 before width relocation. -/
theorem at_shift23 (x y : UInt256) :
    UInt256.land (UInt256.ofNat pairMask)
      (UInt256.add y (UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat 20282409608374036906885615976464) x) (UInt256.ofNat 23))) =
    UInt256.land (UInt256.ofNat pairMask)
      (UInt256.add y (UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat 10141204804187018453442807988232) x) (UInt256.ofNat 22))) := by
  exact rescale x y 10141204804187018453442807988232 23 (by decide) (by decide)

#print axioms at_shift23

/-- Exact multiplier and shift at the site recorded as PC2031 before width relocation. -/
theorem at_shift25 (x y : UInt256) :
    UInt256.land (UInt256.ofNat pairMask)
      (UInt256.add y (UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat 20282409608374036906834076368900) x) (UInt256.ofNat 25))) =
    UInt256.land (UInt256.ofNat pairMask)
      (UInt256.add y (UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat 10141204804187018453417038184450) x) (UInt256.ofNat 24))) := by
  exact rescale x y 10141204804187018453417038184450 25 (by decide) (by decide)

#print axioms at_shift25

/-- Exact multiplier and shift at the site recorded as PC2605 before width relocation. -/
theorem at_shift24 (x y : UInt256) :
    UInt256.land (UInt256.ofNat pairMask)
      (UInt256.add y (UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat 20282409608374036906954335453216) x) (UInt256.ofNat 24))) =
    UInt256.land (UInt256.ofNat pairMask)
      (UInt256.add y (UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat 10141204804187018453477167726608) x) (UInt256.ofNat 23))) := by
  exact rescale x y 10141204804187018453477167726608 24 (by decide) (by decide)

#print axioms at_shift24

/-- Exact multiplier and shift at the site recorded as PC3139 before width relocation. -/
theorem at_shift27 (x y : UInt256) :
    UInt256.land (UInt256.ofNat pairMask)
      (UInt256.add y (UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat 20282409608374036906834076368900) x) (UInt256.ofNat 27))) =
    UInt256.land (UInt256.ofNat pairMask)
      (UInt256.add y (UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat 10141204804187018453417038184450) x) (UInt256.ofNat 26))) := by
  exact rescale x y 10141204804187018453417038184450 27 (by decide) (by decide)

#print axioms at_shift27

/-- Exact multiplier and shift at the site recorded as PC3667 before width relocation. -/
theorem at_shift20 (x y : UInt256) :
    UInt256.land (UInt256.ofNat pairMask)
      (UInt256.add y (UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat 20282409608374036906834076368900) x) (UInt256.ofNat 20))) =
    UInt256.land (UInt256.ofNat pairMask)
      (UInt256.add y (UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat 10141204804187018453417038184450) x) (UInt256.ofNat 19))) := by
  exact rescale x y 10141204804187018453417038184450 20 (by decide) (by decide)

#print axioms at_shift20

#print axioms masked_eq_of_low_eq
#print axioms low_shift_cancel
#print axioms bitvec_rescale
#print axioms rescale

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedMultiplierRescale
