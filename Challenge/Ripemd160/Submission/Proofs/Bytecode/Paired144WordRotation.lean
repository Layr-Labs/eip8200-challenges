import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144FusedD65All
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CommonFactorPlus
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordSum
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordScale
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144LegacyRotation
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRotation
open EvmSemantics Paired144Core Paired144WordRound PairedLaneUInt256Bridge

theorem bits_wordCompact (x : UInt256) (a b : BitVec 32)
    (hn : normalize (bits x) = pack a b) :
    bits (wordCompact x) = BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<< 72) := by
  have hx : UInt256.land x pairWord = word (pack a b) := by
    apply bits_injective
    simpa only [bits_land,pairWord,bits_word,←normalize_eq_and] using hn
  rw [wordCompact, hx]
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  have hmod : (UInt256.mod (word (pack a b)) compactMaskWord).toNat =
      (pack a b).toNat % ((2 ^ 72 - 1) * 2 ^ 32) := by
    simp only [UInt256.mod, compactMaskWord]
    rfl
  rw [bits_toNat, hmod, pack_toNat, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have hsplit : a.toNat + b.toNat * 2 ^ 144 =
      (a.toNat + b.toNat * 2 ^ 72) + (b.toNat * 2 ^ 40) * ((2 ^ 72 - 1) * 2 ^ 32) := by
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul]
    omega
  have hlt : a.toNat + b.toNat * 2 ^ 72 < (2 ^ 72 - 1) * 2 ^ 32 := by
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at *
    omega
  have hlt2 : a.toNat + b.toNat * 2 ^ 72 < 2 ^ 256 := by
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at *
    omega
  have hb2 : b.toNat * 2 ^ 72 < 2 ^ 256 := by
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at *
    omega
  have ha2 : a.toNat < 2 ^ 256 := by
    simp only [Nat.reducePow] at *
    omega
  have hb3 : b.toNat < 2 ^ 256 := by
    simp only [Nat.reducePow] at *
    omega
  rw [hsplit, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt ha2,
    Nat.mod_eq_of_lt hb3, Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hlt2]

theorem bits_wordShift (x : UInt256) (n : Nat) (hn : n<256) :
    bits (wordShift x n) = (bits x * RootCommonFactorPlusProduct.coefficient) >>> n := by
  rw [wordShift,bits_shr _ n hn,bits_mul]
  rfl

theorem scaled_zero (a b : BitVec 32) :
    Paired144LegacyProduct.scaled a b 0 0 = pack a b := by
  rw [← Paired144WordScale.scaleLow_eq_scaled a b 0 (by decide)]
  simp only [Paired144WordScale.scaleLow, Nat.pow_zero,Nat.sub_self,
    BitVec.zero_mul, BitVec.zero_add]

theorem bits_legacy (x : UInt256) (a b : BitVec 32) (r s : Nat)
    (hr0 : 5≤r) (hr : r≤15) (hs0 : 5≤s) (hs : s≤15)
    (hc : ¬ usesCompact r s) (he : ¬ usesFusedExtra r s)
    (hn : normalize (bits x)=pack a b) :
    bits (wordRotate x r s) = RootCommonFactorPlusRotation.rawRotate a b r s := by
  have h := RootCommonFactorPlusWord.bits_wordLegacy x a b r s hr0 hr hs0 hs hn
  simpa only [wordRotate, if_neg hc, if_neg he, RootCommonFactorPlusWord.wordLegacy,
    wordShift, factorPlusWord, RootCommonFactorPlusWord.wordShift,
    RootCommonFactorPlusWord.factorWord] using h

theorem fused_ne (r s : Nat) (h : usesCompact r s ∨ usesFusedExtra r s) : r ≠ s := by
  intro e
  subst s
  simp [usesCompact, usesFusedExtra] at h
  omega

theorem normalize_rotate_add_general (x : UInt256) (a b e f : BitVec 32) (r s : Nat)
    (hr0 : 5≤r) (hr : r≤15) (hs0 : 5≤s) (hs : s≤15)
    (hn : normalize (bits x)=pack a b) :
    normalize (bits (wordRotate x r s) + pack e f) =
      pack (a.rotateLeft r+e) (b.rotateLeft s+f) := by
  by_cases h : usesCompact r s
  · rw [wordRotate, if_pos h]
    exact RootFusedD65All.current_wordFusedRotate_add_all x a b e f r s hn hr0 hr hs0 hs
      (fused_ne r s (Or.inl h))
  · by_cases he : usesFusedExtra r s
    · rw [wordRotate, if_neg h, if_pos he]
      exact RootFusedD65All.current_wordFusedRotate_add_all x a b e f r s hn hr0 hr hs0 hs
        (fused_ne r s (Or.inr he))
    · rw [bits_legacy x a b r s hr0 hr hs0 hs h he hn]
      exact RootCommonFactorPlusRotation.normalize_rotate_add a b e f r s hr0 hr hs0 hs

theorem normalize_rotate_add (x : UInt256) (a b e f : BitVec 32) (r s : Nat)
    (hr0 : 5≤r) (hr : r≤15) (hs0 : 5≤s) (hs : s≤15)
    (_hc : Paired144CompactInput.compact (bits x) =
      BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<<72))
    (hn : normalize (bits x)=pack a b) :
    normalize (bits (wordRotate x r s) + pack e f) =
      pack (a.rotateLeft r+e) (b.rotateLeft s+f) := by
  exact normalize_rotate_add_general x a b e f r s hr0 hr hs0 hs hn

theorem normalize_rotate_add_of (x : UInt256) (a b e f : BitVec 32) (r s : Nat)
    (hr0 : 5≤r) (hr : r≤15) (hs0 : 5≤s) (hs : s≤15)
    (_hc : usesCompact r s → Paired144CompactInput.compact (bits x) =
      BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<<72))
    (hn : normalize (bits x)=pack a b) :
    normalize (bits (wordRotate x r s) + pack e f) =
      pack (a.rotateLeft r+e) (b.rotateLeft s+f) := by
  exact normalize_rotate_add_general x a b e f r s hr0 hr hs0 hs hn

theorem normalize_wordShift23 (a b : BitVec 32) :
    normalize (bits (wordShift (word (pack a b)) 23)) =
      pack (a.rotateLeft 10) (b.rotateLeft 10) := by
  simpa only [wordShift, factorPlusWord, RootCommonFactorPlusWord.wordShift,
    RootCommonFactorPlusWord.factorWord] using RootCommonFactorPlusWord.normalize_cRotate a b

#print axioms bits_legacy
#print axioms normalize_rotate_add
#print axioms normalize_wordShift23
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRotation
