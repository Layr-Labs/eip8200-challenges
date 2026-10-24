import Challenge.Modexp.Submission.Proofs.CRT.RoundedCRT
set_option warningAsError true
set_option maxHeartbeats 2000000
namespace HistoricalSearch.RoundedWordBridge
open EvmSemantics
open Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.GenericColumn HistoricalSearch.CRTWordBridge
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def carryWord (H lo P low high : UInt256) : UInt256 :=
  UInt256.shiftRight lo low + UInt256.shiftLeft
    (UInt256.shiftRight (UInt256.addMod H (UInt256.lnot lo) P) (UInt256.ofNat 5)) high

theorem lnot_toNat (a : UInt256) : (UInt256.lnot a).toNat = 2^256-1-a.toNat := by
  unfold UInt256.lnot UInt256.size
  rw [word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := a.val.isLt; omega)

theorem addMod_toNat (a b P : UInt256) (hP : 0 < P.toNat) :
    (UInt256.addMod a b P).toNat = (a.toNat+b.toNat) % P.toNat := by
  have hPn : P.val.val ≠ 0 := by change P.toNat ≠ 0; omega
  unfold UInt256.addMod
  rw [if_neg hPn, word_toNat_ofNat]
  exact Nat.mod_eq_of_lt ((Nat.mod_lt _ hP).trans P.val.isLt)

theorem carryWord_toNat (W S C H : Nat) (hWpos : 0 < W) (hW : W ≤ 248)
    (hC : C ≤ 18*(2^W-1)) (hS : S ≤ 18*(2^W-1)^2+C)
    (hHR : H < wordRadix) (hH : H % residueModulus = S % residueModulus) :
    (carryWord (UInt256.ofNat H) (UInt256.ofNat (S % wordRadix))
      (UInt256.ofNat residueModulus) (UInt256.ofNat W) (UInt256.ofNat (256-W))).toNat = S/2^W := by
  have hp : 0 < residueModulus := by norm_num [residueModulus]
  have hpR : residueModulus < wordRadix := by norm_num [residueModulus, wordRadix]
  have hloR : S % wordRadix < wordRadix := Nat.mod_lt _ (by norm_num [wordRadix])
  have hHv : (UInt256.ofNat H).toNat = H := by
    rw [word_toNat_ofNat]; exact Nat.mod_eq_of_lt hHR
  have hlov : (UInt256.ofNat (S % wordRadix)).toNat = S % wordRadix := by
    rw [word_toNat_ofNat]; exact Nat.mod_eq_of_lt hloR
  have hPv : (UInt256.ofNat residueModulus).toNat = residueModulus := by
    rw [word_toNat_ofNat]; exact Nat.mod_eq_of_lt hpR
  have hPpos : 0 < (UInt256.ofNat residueModulus).toNat := by rw [hPv]; exact hp
  have hq := HistoricalSearch.RoundedCRT.roundedHigh wordRadix residueModulus 32 S H
    (by norm_num [wordRadix]) hp (by decide) (by norm_num [wordRadix,residueModulus])
    hH (HistoricalSearch.RoundedCRT.roundedWidthBound W S C hW hC hS)
  have hr : wordRadix = 2^W * 2^(256-W) := by
    rw [wordRadix, ← Nat.pow_add, Nat.add_sub_of_le (by omega : W ≤ 256)]
  have hsplit : (S % wordRadix)/2^W+S/wordRadix*2^(256-W) = S/2^W := by
    rw [hr]; exact carryFromHigh (2^W) (2^(256-W)) S (Nat.two_pow_pos W)
  have hc := columnCarryBound (2^W) 18 S C (Nat.two_pow_pos W) hC hS
  have hpow : 2^W ≤ (2^248 : Nat) := Nat.pow_le_pow_right (by decide) hW
  have hcarrylt : S/2^W < wordRadix := by norm_num [wordRadix] at *; omega
  have hqshift : S/wordRadix*2^(256-W) < wordRadix := by
    calc S/wordRadix*2^(256-W) ≤ (S % wordRadix)/2^W+S/wordRadix*2^(256-W) := Nat.le_add_left _ _
      _ = S/2^W := hsplit
      _ < wordRadix := hcarrylt
  unfold carryWord
  rw [word_toNat_add, shiftRight_toNat _ (by omega : W < 256), hlov,
    shiftLeft_toNat _ (256-W) (by omega), shiftRight_toNat _ (by decide : 5 < 256),
    addMod_toNat _ _ _ hPpos, lnot_toNat, hHv, hlov, hPv]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change ((S % wordRadix)/2^W + (((H+(wordRadix-1-S%wordRadix))%residueModulus)/32*2^(256-W))%wordRadix)%wordRadix = _
  rw [hq, Nat.mod_eq_of_lt hqshift, hsplit, Nat.mod_eq_of_lt hcarrylt]

#print axioms carryWord_toNat
end HistoricalSearch.RoundedWordBridge
