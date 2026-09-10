import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneProduct

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneRotate

open PairedLaneCore PairedLaneProduct

theorem get_pack_low (a b : BitVec 32) (i : Nat) (hi : i < 128) :
    (pack a b).getLsbD i = a.getLsbD i := by
  simp only [pack, BitVec.getLsbD_append, hi, ite_true,
    BitVec.getLsbD_setWidth, decide_true, Bool.true_and]

theorem get_pack_high (a b : BitVec 32) (i : Nat)
    (hlo : 128 ≤ i) (hi : i < 256) :
    (pack a b).getLsbD i = b.getLsbD (i - 128) := by
  have hn : ¬ i < 128 := by omega
  have hs : i - 128 < 128 := by omega
  simp only [pack, BitVec.getLsbD_append, hn, ite_false,
    BitVec.getLsbD_setWidth, hs, decide_true, Bool.true_and]

theorem factor_pack (a b : BitVec 32) :
    pack a b * factor = (pack a b <<< 32) ||| pack a b := by
  simpa only [normalize_pack] using factor_copies_normalized (pack a b)

theorem low_rotate_product (a b : BitVec 32) (r : Nat)
    (hr0 : 0 < r) (hr : r < 32) :
    low ((pack a b * factor) >>> (32 - r)) = a.rotateLeft r := by
  rw [factor_pack]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ht : 32 - r + i < 128 := by omega
  have ht256 : 32 - r + i < 256 := by omega
  have hsub : 32 - r + i - 32 < 128 := by omega
  simp only [low, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, Nat.zero_add, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    ht256, decide_true, Bool.true_and, get_pack_low a b _ ht,
    get_pack_low a b _ hsub, BitVec.getLsbD_rotateLeft_of_le hr]
  by_cases h : i < r
  · have hp : 32 - r + i < 32 := by omega
    simp [h, hp]
  · have hp : ¬ 32 - r + i < 32 := by omega
    have he : 32 - r + i - 32 = i - r := by omega
    rw [BitVec.getLsbD_of_ge a _ (by omega : 32 ≤ 32 - r + i)]
    simp [h, hp, he]

/-- The high cell's preceding 96-bit spacer excludes the low lane. -/
theorem high_rotate_product (a b : BitVec 32) (r : Nat)
    (hr0 : 0 < r) (hr : r < 32) :
    high ((pack a b * factor) >>> (32 - r)) = b.rotateLeft r := by
  rw [factor_pack]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hp0 : 128 ≤ 32 - r + (128 + i) := by omega
  have hp1 : 32 - r + (128 + i) < 256 := by omega
  have hp2 : ¬ 32 - r + (128 + i) < 32 := by omega
  have he : 32 - r + (128 + i) - 128 = 32 - r + i := by omega
  simp only [high, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, hp1, hp2, decide_true, decide_false,
    Bool.not_false, Bool.true_and, get_pack_high a b _ hp0 hp1,
    he, BitVec.getLsbD_rotateLeft_of_le hr]
  by_cases h : i < r
  · have hlow : 32 - r + (128 + i) - 32 < 128 := by omega
    rw [get_pack_low a b _ hlow,
      BitVec.getLsbD_of_ge a _ (by omega : 32 ≤ 32 - r + (128 + i) - 32)]
    simp [h]
  · have hhigh : 128 ≤ 32 - r + (128 + i) - 32 := by omega
    have hhigh' : 32 - r + (128 + i) - 32 < 256 := by omega
    have he' : 32 - r + (128 + i) - 32 - 128 = i - r := by omega
    rw [get_pack_high a b _ hhigh hhigh', he',
      BitVec.getLsbD_of_ge b _ (by omega : 32 ≤ 32 - r + i)]
    simp [h]

theorem normalize_rotate_product (a b : BitVec 32) (r : Nat)
    (hr0 : 0 < r) (hr : r < 32) :
    normalize ((pack a b * factor) >>> (32 - r)) =
      pack (a.rotateLeft r) (b.rotateLeft r) := by
  rw [normalize, low_rotate_product a b r hr0 hr,
    high_rotate_product a b r hr0 hr]

#print axioms factor_pack
#print axioms low_rotate_product
#print axioms high_rotate_product
#print axioms normalize_rotate_product

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneRotate
