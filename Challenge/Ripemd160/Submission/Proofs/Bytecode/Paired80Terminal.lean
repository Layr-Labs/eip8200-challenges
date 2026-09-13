import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80GapCarry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80ScaledRotate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Message

set_option warningAsError true
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Terminal
open Paired80Core Paired80Boolean Paired80ScaledRotate

theorem clean_gap (x : BitVec 256) (hx : normalize x = x) : x.getLsbD 48 = false := by
  rw [← hx, normalize_eq_and, BitVec.getLsbD_and]
  have h : pairMask.getLsbD 48 = false := by decide
  simp only [h, Bool.and_false]

/-- The unmasked round78 T retains the carry-separating bit. -/
theorem scaled78_add_gap (a b e f : BitVec 32) :
    (pack e f + ((scaleHigh (pack a b) 6 * Paired80Product.factor) >>> 27)).getLsbD 48 = false := by
  rw [← BitVec.testBit_toNat, BitVec.toNat_add, pack_toNat, toNat_shift,
    scaleHigh_product_toNat a b 6 (by decide)]
  have ha := a.isLt
  have hb := b.isLt
  have he := e.isLt
  have hf := f.isLt
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [Nat.reducePow] at *
  apply decide_eq_false_iff_not.mpr
  omega

theorem c10_gap (a b : BitVec 32) :
    ((pack a b * Paired80Product.factor) >>> 22).getLsbD 48 = false :=
  Paired80Carry.shifted_product_gap a b 10 (by decide) (by decide)

theorem clean_low (x : BitVec 256) (hx : normalize x = x) : x.toNat % 2 ^ 80 < 2 ^ 32 := by
  rw [← hx, normalize, pack_toNat]
  have h := (low x).isLt
  simp only [Nat.reducePow] at *
  omega

theorem message_low (x : BitVec 256) (a b : BitVec 32)
    (hx : Paired80Message.Eq112 x (pack a b)) : x.toNat % 2 ^ 80 < 2 ^ 32 := by
  unfold Paired80Message.Eq112 at hx
  rw [pack_toNat] at hx
  have ha := a.isLt
  have hb := b.isLt
  simp only [Nat.reducePow] at *
  omega

theorem three_small (x y z : BitVec 256)
    (hx : x.toNat % 2 ^ 80 < 2 ^ 32)
    (hy : y.toNat % 2 ^ 80 < 2 ^ 32)
    (hz : z.toNat % 2 ^ 80 < 2 ^ 32) :
    (x + (y + z)).toNat % 2 ^ 80 < 2 ^ 47 := by
  simp only [BitVec.toNat_add, Nat.reducePow] at *
  omega

def inline4 (b c d : BitVec 256) : BitVec 256 :=
  (lowerMask &&& (d ||| ~~~c)) ^^^ (d ^^^ (c ^^^ b))

theorem inline4_mask (b c d : BitVec 256) (hc : normalize c = c) :
    normalize (inline4 b c d) = inline4 (normalize b) c (normalize d) := by
  have hc' : pairMask &&& c = c := by rw [BitVec.and_comm, ← normalize_eq_and, hc]
  have hlp : pairMask &&& lowerMask = lowerMask := by decide
  simp only [inline4, normalize_eq_and]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hcl := congrArg (fun x : BitVec 256 => x.getLsbD i) hc'
  have hl := congrArg (fun x : BitVec 256 => x.getLsbD i) hlp
  simp only [BitVec.getLsbD_and] at hcl hl
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases hp : pairMask.getLsbD i <;> cases hl0 : lowerMask.getLsbD i <;>
    cases hb0 : b.getLsbD i <;> cases hc0 : c.getLsbD i <;> cases hd0 : d.getLsbD i <;>
    simp_all

theorem inline4_gap (b c d : BitVec 256)
    (hb : b.getLsbD 48 = false) (hc : c.getLsbD 48 = false) (hd : d.getLsbD 48 = false) :
    (inline4 b c d).getLsbD 48 = false := by
  have hl : lowerMask.getLsbD 48 = false := by decide
  simp only [inline4, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hl, hb, hc, hd]
  rfl

/-- Round79 sees the same masked sum after normalizing the two dirty outputs
of round78. The other addends need only a low80 bound, so table high bits remain free. -/
theorem terminal_sum_masked (b c d rest : BitVec 256)
    (hc : normalize c = c) (hb : b.getLsbD 48 = false) (hd : d.getLsbD 48 = false)
    (hs : rest.toNat % 2 ^ 80 < 2 ^ 47) :
    normalize (inline4 b c d + rest) =
      normalize (inline4 (normalize b) c (normalize d) + rest) := by
  rw [Paired80GapCarry.normalize_add_gap _ _ hs
    (inline4_gap b c d hb (clean_gap c hc) hd), inline4_mask b c d hc]

#print axioms scaled78_add_gap
#print axioms c10_gap
#print axioms message_low
#print axioms terminal_sum_masked
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Terminal
