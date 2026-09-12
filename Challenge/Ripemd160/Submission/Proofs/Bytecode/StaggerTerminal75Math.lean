import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerWord

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTerminal75Math
open Paired144Core

theorem add_small_no_carry144 (x : BitVec 144) (e : Nat)
    (he : e < 2 ^ 120) (hgap : x.getLsbD 121 = false) :
    x.toNat + e < 2 ^ 144 := by
  have hx := x.isLt
  have hbit : ¬ x.toNat / 2 ^ 121 % 2 = 1 := by
    simpa only [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
      decide_eq_false_iff_not] using hgap
  simp only [Nat.reducePow] at *
  omega

theorem high_add_general (x y : Nat)
    (hcarry : x % 2 ^ 144 + y % 2 ^ 144 < 2 ^ 144) :
    ((x + y) % 2 ^ 256) / 2 ^ 144 % 2 ^ 32 =
      (x / 2 ^ 144 % 2 ^ 32 + y / 2 ^ 144 % 2 ^ 32) % 2 ^ 32 := by
  simp only [Nat.reducePow] at *
  omega

theorem normalize_add_gap (x y : BitVec 256)
    (hy : y.toNat % 2 ^ 144 < 2 ^ 120) (hgap : x.getLsbD 121 = false) :
    normalize (x + y) = normalize (normalize x + y) := by
  have hgap' : (x.extractLsb' 0 144).getLsbD 121 = false := by
    simpa only [BitVec.getLsbD_extractLsb', Nat.zero_add,
      show decide (121 < 144) = true from rfl, Bool.true_and] using hgap
  have hcarry : x.toNat % 2 ^ 144 + y.toNat % 2 ^ 144 < 2 ^ 144 := by
    simpa only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] using
      add_small_no_carry144 (x.extractLsb' 0 144) (y.toNat % 2 ^ 144) hy hgap'
  have hnorm : (normalize x).toNat % 2 ^ 144 < 2 ^ 32 := by
    rw [normalize, pack_toNat]
    have hlo := (low x).isLt
    simp only [Nat.reducePow] at *
    omega
  have hcarry' : (normalize x).toNat % 2 ^ 144 + y.toNat % 2 ^ 144 < 2 ^ 144 := by
    simp only [Nat.reducePow] at *
    omega
  have hlo : low (x + y) = low (normalize x + y) := by
    change (x + y).extractLsb' 0 32 = (normalize x + y).extractLsb' 0 32
    rw [BitVec.extractLsb'_add (by decide), BitVec.extractLsb'_add (by decide)]
    change low x + low y = low (pack (low x) (high x)) + low y
    rw [low_pack]
  have hhi : high (x + y) = high (normalize x + y) := by
    apply BitVec.eq_of_toNat_eq
    simp only [high, BitVec.extractLsb'_toNat, BitVec.toNat_add,
      Nat.shiftRight_eq_div_pow]
    rw [high_add_general _ _ hcarry, high_add_general _ _ hcarry']
    have hn : (normalize x).toNat / 2 ^ 144 % 2 ^ 32 = x.toNat / 2 ^ 144 % 2 ^ 32 := by
      have h := congrArg BitVec.toNat (high_pack (low x) (high x))
      simpa only [high, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, normalize] using h
    rw [hn]
  change pack (low (x + y)) (high (x + y)) = pack (low (normalize x + y)) (high (normalize x + y))
  rw [hlo, hhi]

#print axioms normalize_add_gap


open EvmSemantics PairedLaneUInt256Bridge Paired144WordRound Paired144WordRotation

theorem three_small (a b c d e f : BitVec 32) :
    ((pack a b + pack c d) + pack e f).toNat % 2^144 < 2^120 := by
  simp only [BitVec.toNat_add, pack_toNat]
  have ha:=a.isLt
  have hc:=c.isLt
  have he:=e.isLt
  simp only [Nat.reducePow] at *
  omega

theorem pack_gap (a b : BitVec 32) : (pack a b).getLsbD 121 = false := by
  simp only [pack, BitVec.getLsbD_append, show 121 < 144 from by decide,
    ite_true, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge a 121 (by decide : 32 ≤ 121),
    Bool.and_false]

theorem c_gap (a b : BitVec 32) :
    (bits (wordShift (word (pack a b)) 28)).getLsbD 121 = false := by
  rw [bits_wordShift _ _ (by decide), bits_word, ← scaled_zero a b]
  exact Paired144LegacyProduct.shiftedProduct_gap a b 0 0 28 (by decide) (by decide)

theorem raw4_normalize_d (sel b c d : UInt256) :
    normalize (bits (StaggerWord.raw 4 sel b c d)) =
    normalize (bits (StaggerWord.raw 4 sel b c (UInt256.land d pairWord))) := by
  simp only [StaggerWord.raw,bits_xor,bits_lor,bits_land,pairWord,bits_word,
    normalize_eq_and]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_or]
  cases pairMask.getLsbD i <;> simp

theorem raw4_gap (b c d : UInt256)
    (hb : (bits b).getLsbD 121 = false)
    (hc : (bits c).getLsbD 121 = false)
    (hd : (bits d).getLsbD 121 = false) :
    (bits (StaggerWord.raw 4 (StaggerWord.selector 4) b c d)).getLsbD 121 = false := by
  have hs : (bits (StaggerWord.selector 4)).getLsbD 121 = false := by decide
  simp only [StaggerWord.raw,bits_xor,bits_lor,bits_land,
    BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_or,hb,hc,hd,hs]
  rfl

theorem masked_gap (x : UInt256) :
    (bits (UInt256.land x pairWord)).getLsbD 121 = false := by
  simp only [bits_land,pairWord,bits_word,BitVec.getLsbD_and]
  have h : pairMask.getLsbD 121 = false := by decide
  simp only [h,Bool.and_false]

#print axioms three_small
#print axioms pack_gap
#print axioms c_gap
#print axioms raw4_normalize_d
#print axioms raw4_gap


theorem normalize_add_change (x x' y : BitVec 256)
    (hy : y.toNat % 2^144 < 2^120)
    (hx : x.getLsbD 121 = false) (hx' : x'.getLsbD 121 = false)
    (he : normalize x = normalize x') :
    normalize (x+y) = normalize (x'+y) := by
  rw [normalize_add_gap x y hy hx,normalize_add_gap x' y hy hx',he]

theorem sum_normalize_d (l r : CryptoLane) (d : UInt256)
    (wl wr kl kr : BitVec 32) (hd : (bits d).getLsbD 121 = false) :
    normalize (bits (StaggerWord.sum 4 (packCrypto l r).a (packCrypto l r).b
      (packCrypto l r).c d (word (pack wl wr)) (word (pack kl kr)))) =
    normalize (bits (StaggerWord.sum 4 (packCrypto l r).a (packCrypto l r).b
      (packCrypto l r).c (UInt256.land d pairWord)
      (word (pack wl wr)) (word (pack kl kr)))) := by
  have hb : (bits (packCrypto l r).b).getLsbD 121 = false := by
    change (bits (word (pack _ _))).getLsbD 121 = false
    rw [bits_word]
    exact pack_gap _ _
  have hc : (bits (packCrypto l r).c).getLsbD 121 = false := by
    change (bits (word (pack _ _))).getLsbD 121 = false
    rw [bits_word]
    exact pack_gap _ _
  let y := (bits (packCrypto l r).a + pack wl wr) + pack kl kr
  have hy : y.toNat % 2^144 < 2^120 := by
    change ((bits (word (pack _ _)) + pack wl wr) + pack kl kr).toNat % 2^144 < 2^120
    rw [bits_word]
    exact three_small _ _ _ _ _ _
  have h := normalize_add_change
    (bits (StaggerWord.raw 4 (StaggerWord.selector 4) (packCrypto l r).b (packCrypto l r).c d))
    (bits (StaggerWord.raw 4 (StaggerWord.selector 4) (packCrypto l r).b
      (packCrypto l r).c (UInt256.land d pairWord))) y hy
    (raw4_gap _ _ _ hb hc hd) (raw4_gap _ _ _ hb hc (masked_gap d))
    (raw4_normalize_d _ _ _ _)
  simp only [StaggerWord.sum,bits_add,bits_word]
  convert h using 1 <;> congr 1 <;> dsimp only [y] <;> ac_rfl


theorem mask_eq_of_normalize (x y : UInt256)
    (h : normalize (bits x) = normalize (bits y)) :
    UInt256.land x pairWord = UInt256.land y pairWord := by
  apply bits_injective
  simpa only [bits_land,pairWord,bits_word,← normalize_eq_and] using h

theorem rotate11 (x : UInt256) :
    wordRotate x 11 11 = wordShift (UInt256.land x pairWord) 27 := by
  unfold wordRotate
  rw [if_neg (by decide : ¬ usesCompact 11 11), if_pos rfl]

theorem t_d_eq (l r : CryptoLane) (d : UInt256) (wl wr kl kr : BitVec 32)
    (hd : (bits d).getLsbD 121 = false)
    (he : UInt256.land d pairWord = (packCrypto l r).d) :
    StaggerWord.t 4 11 11 (word (pack wl wr)) (word (pack kl kr))
      {packCrypto l r with d:=d} =
    StaggerWord.t 4 11 11 (word (pack wl wr)) (word (pack kl kr)) (packCrypto l r) := by
  have h := sum_normalize_d l r d wl wr kl kr hd
  have hn := h.trans (congrArg (fun z : UInt256 => normalize (bits
    (StaggerWord.sum 4 (packCrypto l r).a (packCrypto l r).b
      (packCrypto l r).c z (word (pack wl wr)) (word (pack kl kr))))) he)
  have hs := mask_eq_of_normalize _ _ hn
  change UInt256.land (UInt256.add (wordRotate
    (StaggerWord.sum 4 (packCrypto l r).a (packCrypto l r).b
      (packCrypto l r).c d (word (pack wl wr)) (word (pack kl kr))) 11 11)
        (packCrypto l r).e) pairWord = _
  simp only [StaggerWord.t,rotate11]
  exact congrArg (fun z : UInt256 => UInt256.land
    (UInt256.add (wordShift z 27) (packCrypto l r).e) pairWord) hs

#print axioms sum_normalize_d
#print axioms t_d_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTerminal75Math
