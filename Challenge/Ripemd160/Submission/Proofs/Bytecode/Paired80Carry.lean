import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Rotate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Boolean
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80SumsBase

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Carry

open Paired80Core Paired80Product Paired80Rotate Paired80Boolean

/-- A zero spacer bit alone prevents a 32-bit addend crossing bit 80. -/
theorem add32_no_carry80 (x : BitVec 80) (e : BitVec 32)
    (hgap : x.getLsbD 48 = false) :
    x.toNat + e.toNat < 2 ^ 80 := by
  have hx := x.isLt
  have he := e.isLt
  have hbit : ¬ x.toNat / 2 ^ 48 % 2 = 1 := by
    simpa only [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
      decide_eq_false_iff_not] using hgap
  simp only [Nat.reducePow] at *
  omega

theorem shifted_product_gap (a b : BitVec 32) (r : Nat)
    (hr0 : 0 < r) (hr : r < 17) :
    ((pack a b * factor) >>> (32 - r)).getLsbD 48 = false := by
  rw [factor_pack, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  have hp : 32 - r + 48 < 80 := by omega
  have hm : 32 - r + 48 - 32 < 80 := by omega
  rw [get_pack_low a b _ hp, get_pack_low a b _ hm,
    BitVec.getLsbD_of_ge a _ (by omega : 32 ≤ 32 - r + 48),
    BitVec.getLsbD_of_ge a _ (by omega : 32 ≤ 32 - r + 48 - 32)]
  simp only [Bool.and_false, Bool.or_false]

def blend (x y : BitVec 256) : BitVec 256 :=
  x ^^^ ((x ^^^ y) &&& upperMask)

theorem blend_gap (x y : BitVec 256) (hx : x.getLsbD 48 = false) :
    (blend x y).getLsbD 48 = false := by
  have hm : upperMask.getLsbD 48 = false := by decide
  simp only [blend, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    hm, hx, Bool.and_false, Bool.xor_false]

theorem blend_shifted_gap (a b : BitVec 32) (r s : Nat)
    (hr0 : 0 < r) (hr : r < 17) :
    (blend ((pack a b * factor) >>> (32 - r))
      ((pack a b * factor) >>> (32 - s))).getLsbD 48 = false := by
  exact blend_gap _ _ (shifted_product_gap a b r hr0 hr)

#print axioms add32_no_carry80
#print axioms shifted_product_gap
#print axioms blend_gap
#print axioms blend_shifted_gap

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Carry
