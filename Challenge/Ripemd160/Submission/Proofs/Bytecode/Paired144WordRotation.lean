import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordSum
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordScale
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144LegacyRotation
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRotation
open EvmSemantics Paired144Core Paired144WordRound PairedLaneUInt256Bridge

theorem bits_wordCompact (x : UInt256) :
    bits (wordCompact x) = Paired144CompactInput.compact (bits x) := by
  simp only [wordCompact,compactMaskWord,Paired144CompactInput.compact,
    bits_land,bits_lor,bits_shr x 72 (by decide),bits_ofNat]

theorem bits_wordShift (x : UInt256) (n : Nat) (hn : n<256) :
    bits (wordShift x n) = (bits x * Paired144LegacyProduct.coefficient) >>> n := by
  rw [wordShift,bits_shr _ n hn,bits_mul]
  rfl

theorem scaled_zero (a b : BitVec 32) :
    Paired144LegacyProduct.scaled a b 0 0 = pack a b := by
  rw [← Paired144WordScale.scaleLow_eq_scaled a b 0 (by decide)]
  simp only [Paired144WordScale.scaleLow, Nat.pow_zero,Nat.sub_self,
    BitVec.zero_mul, BitVec.zero_add]

theorem bits_legacy (x : UInt256) (a b : BitVec 32) (r s : Nat)
    (hr0 : 5≤r) (hr : r≤15) (hs0 : 5≤s) (hs : s≤15)
    (hc : ¬ usesCompact r s) (hn : normalize (bits x)=pack a b) :
    bits (wordRotate x r s) = Paired144LegacyRotation.rawRotate a b r s := by
  have hx : UInt256.land x pairWord = word (pack a b) := by
    apply bits_injective
    simpa only [bits_land,pairWord,bits_word,←normalize_eq_and] using hn
  rw [wordRotate,if_neg hc,hx]
  by_cases he : r=s
  · subst s
    rw [if_pos rfl,bits_wordShift _ _ (by omega),bits_word]
    simp only [Paired144LegacyRotation.rawRotate,Paired144LegacyProduct.rawProduct,
      Nat.sub_self,Nat.min_self,scaled_zero]
  · rw [if_neg he]
    by_cases hlt : s<r
    · rw [if_pos hlt,bits_wordShift _ _ (by omega),
        Paired144WordScale.bits_wordScale_lower a b (r-s) (by omega)]
      simp only [Paired144LegacyRotation.rawRotate,Paired144LegacyProduct.rawProduct,
        Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt),Nat.min_eq_right (Nat.le_of_lt hlt)]
    · rw [if_neg hlt,bits_wordShift _ _ (by omega),
        Paired144WordScale.bits_wordScale_upper a b (s-r) (by omega)]
      have hle : r≤s := by omega
      simp only [Paired144LegacyRotation.rawRotate,Paired144LegacyProduct.rawProduct,
        Nat.sub_eq_zero_of_le hle,Nat.min_eq_left hle]

theorem normalize_rotate_add (x : UInt256) (a b e f : BitVec 32) (r s : Nat)
    (hr0 : 5≤r) (hr : r≤15) (hs0 : 5≤s) (hs : s≤15)
    (hc : Paired144CompactInput.compact (bits x) =
      BitVec.ofNat 256 a.toNat + (BitVec.ofNat 256 b.toNat <<<72))
    (hn : normalize (bits x)=pack a b) :
    normalize (bits (wordRotate x r s) + pack e f) =
      pack (a.rotateLeft r+e) (b.rotateLeft s+f) := by
  by_cases h : usesCompact r s
  · have hsr := h.1
    have hd := h.2
    have hu : r-s≤7 := by rcases hd with h|h|h <;> omega
    have hr' : 32+(r-s)-(32-s)=r := by omega
    have hs' : 32+0-(32-s)=s := by omega
    rw [wordRotate,if_pos h,bits_shr _ (32-s) (by omega),bits_mul,bits_wordCompact,hc]
    change normalize ((Paired144CompactGap.rawProduct a b (r-s) 0 >>> (32-s))+pack e f)=_
    simpa only [hr',hs'] using
      Paired144CompactRotation.normalize_shifted_add a b e f (r-s) 0 (32-s)
        hu (by decide) (by omega) (by omega)
  · rw [bits_legacy x a b r s hr0 hr hs0 hs h hn]
    exact Paired144LegacyRotation.normalize_rotate_add a b e f r s hr0 hr hs0 hs

theorem normalize_wordShift28 (a b : BitVec 32) :
    normalize (bits (wordShift (word (pack a b)) 28)) =
      pack (a.rotateLeft 10) (b.rotateLeft 10) := by
  rw [bits_wordShift _ 28 (by decide),bits_word,←scaled_zero a b]
  exact Paired144LegacyRotation.normalize_cRotate a b

#print axioms bits_legacy
#print axioms normalize_rotate_add
#print axioms normalize_wordShift28
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRotation
