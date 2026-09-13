import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Rotate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Message

set_option warningAsError true
set_option maxRecDepth 2048
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TerminalTranspose
open Paired80Core Paired80Product Paired80Rotate

def wideFactor : BitVec 256 := factor * (BitVec.twoPow 256 155 + 1#256)

theorem wideFactor_value : wideFactor =
    BitVec.ofNat 256 196159429276505700036459135669104726525582452008043937793 := by
  decide

theorem mul_truncate (x : BitVec 256) :
    (x * wideFactor).setWidth 155 = (x * factor).setWidth 155 := by
  rw [BitVec.setWidth_mul _ _ (by decide), BitVec.setWidth_mul _ _ (by decide)]
  have hc : wideFactor.setWidth 155 = factor.setWidth 155 := by decide
  rw [hc]

theorem wide_bit (x : BitVec 256) (i : Nat) (hi : i < 155) :
    (x * wideFactor).getLsbD i = (x * factor).getLsbD i := by
  have h := congrArg (fun (v : BitVec 155) => v.getLsbD i) (mul_truncate x)
  simpa only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and] using h

theorem shift_truncate (x : BitVec 256) (s : Nat) (hs : s ≤ 43) :
    (((x * wideFactor) >>> s).setWidth 112) =
      (((x * factor) >>> s).setWidth 112) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight]
  exact wide_bit x _ (by omega)

theorem eq112_wide_shift (x : BitVec 256) (s : Nat) (hs : s ≤ 43) :
    Paired80Message.Eq112 ((x * wideFactor) >>> s) ((x * factor) >>> s) := by
  have h := congrArg BitVec.toNat (shift_truncate x s hs)
  simpa only [Paired80Message.Eq112, BitVec.toNat_setWidth] using h

#print axioms eq112_wide_shift

/-- All ordinary shifts observe exactly the original two active cells. -/
theorem normalize_wide_shift (x : BitVec 256) (s : Nat) (hs : s ≤ 43) :
    normalize ((x * wideFactor) >>> s) = normalize ((x * factor) >>> s) := by
  have hl : low ((x * wideFactor) >>> s) = low ((x * factor) >>> s) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [low, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
      Nat.zero_add, BitVec.getLsbD_ushiftRight]
    exact wide_bit x _ (by omega)
  have hh : high ((x * wideFactor) >>> s) = high ((x * factor) >>> s) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [high, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
      BitVec.getLsbD_ushiftRight]
    exact wide_bit x _ (by omega)

  unfold normalize
  rw [hl, hh]

theorem factor_high_zero (a b : BitVec 32) (i : Nat) (hi : 144 ≤ i) :
    (pack a b * factor).getLsbD i = false := by
  by_cases hw : i < 256
  · rw [factor_pack, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    have h32 : ¬ i < 32 := by omega
    have h80 : 80 ≤ i := by omega
    have hs80 : 80 ≤ i - 32 := by omega
    have hs256 : i - 32 < 256 := by omega
    rw [get_pack_high a b i h80 hw, get_pack_high a b (i-32) hs80 hs256,
      BitVec.getLsbD_of_ge b _ (by omega : 32 ≤ i - 80),
      BitVec.getLsbD_of_ge b _ (by omega : 32 ≤ i - 32 - 80)]
    simp only [h32, decide_false, Bool.not_false,
      Bool.and_false, Bool.or_false]
  · exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem product_images_disjoint (a b : BitVec 32) :
    (pack a b * factor) &&& ((pack a b * factor) <<< 155) = 0#256 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  by_cases hs : i < 155
  · simp [hs]
  · rw [factor_high_zero a b i (by omega)]
    simp

theorem wide_pack_product (a b : BitVec 32) :
    pack a b * wideFactor = (pack a b * factor) |||
      ((pack a b * factor) <<< 155) := by
  unfold wideFactor
  rw [← BitVec.mul_assoc, BitVec.mul_add, BitVec.mul_twoPow_eq_shiftLeft,
    BitVec.mul_one, BitVec.add_comm]
  exact BitVec.add_eq_or_of_and_eq_zero _ _ (product_images_disjoint a b)


theorem terminal_low (a b : BitVec 32) :
    low ((pack a b * wideFactor) >>> 101) = b.rotateLeft 11 := by
  rw [← high_rotate_product a b 11 (by decide) (by decide)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [low, high, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, Nat.zero_add, BitVec.getLsbD_ushiftRight, wide_pack_product,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h : 101 + i < 155 := by omega
  have hw : 101 + i < 256 := by omega
  have he : 32 - 11 + (80 + i) = 101 + i := by omega
  simp only [h, hw, decide_true, Bool.not_true, Bool.and_false, Bool.false_and,
    Bool.or_false, he]

theorem terminal_high (a b : BitVec 32) :
    high ((pack a b * wideFactor) >>> 101) = a.rotateLeft 6 := by
  rw [← low_rotate_product a b 6 (by decide) (by decide)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [low, high, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, Nat.zero_add, BitVec.getLsbD_ushiftRight, wide_pack_product,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h : ¬ 101 + (80+i) < 155 := by omega
  have hw : 101 + (80+i) < 256 := by omega
  have he : 101 + (80+i) - 155 = 32 - 6 + i := by omega
  rw [factor_high_zero a b _ (by omega)]
  simp only [h, hw, decide_false, decide_true, Bool.not_false, Bool.true_and,
    Bool.false_or, he]

theorem normalize_terminal (a b : BitVec 32) :
    normalize ((pack a b * wideFactor) >>> 101) =
      pack (b.rotateLeft 11) (a.rotateLeft 6) := by
  simp only [normalize, terminal_low, terminal_high]

#print axioms normalize_terminal

#print axioms mul_truncate
#print axioms normalize_wide_shift
#print axioms wide_pack_product
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TerminalTranspose
