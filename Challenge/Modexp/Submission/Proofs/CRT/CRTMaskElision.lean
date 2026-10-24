import Challenge.Modexp.Submission.Proofs.CRT.WordCancellation
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace HistoricalSearch.CRTMaskElision
open EvmSemantics Challenge.EvmProof.Word
open HistoricalSearch.WordCancellation
open HistoricalSearch.CRTColumn HistoricalSearch.ProductAccumulate

/-- Keeping the low W bits after multiplication makes an earlier truncation
of either factor redundant, including when the 256-bit product wraps. -/
theorem mask_mul_mask (lo inv : UInt256) (W F : Nat) (hFW : F ≤ W) (hW : W ≤ 256) :
    UInt256.land (UInt256.ofNat (2^F-1))
      (inv * UInt256.land (UInt256.ofNat (2^W-1)) lo) =
    UInt256.land (UInt256.ofNat (2^F-1)) (inv * lo) := by
  apply word_ext
  rw [land_comm (UInt256.ofNat (2^F-1)),
      land_comm (UInt256.ofNat (2^F-1)),
      land_comm (UInt256.ofNat (2^W-1))]
  change ((inv*(lo &&& UInt256.ofNat (2^W-1))) &&&
    UInt256.ofNat (2^F-1)).toNat =
    ((inv*lo) &&& UInt256.ofNat (2^F-1)).toNat
  rw [mask_toNat _ F (hFW.trans hW), mask_toNat _ F (hFW.trans hW), mul_toNat, mul_toNat,
      mask_toNat _ W hW]
  have hd : (2^F : Nat) ∣ 2^256 := Nat.pow_dvd_pow 2 (hFW.trans hW)
  have hdfw : (2^F : Nat) ∣ 2^W := Nat.pow_dvd_pow 2 hFW
  rw [Nat.mod_mod_of_dvd _ hd, Nat.mod_mod_of_dvd _ hd]
  rw [Nat.mul_mod, Nat.mod_mod_of_dvd _ hdfw, ← Nat.mul_mod]

theorem mask244_mul_mask244 (lo inv : UInt256) :
    UInt256.land (UInt256.ofNat (2^244-1))
      (inv * UInt256.land (UInt256.ofNat (2^244-1)) lo) =
    UInt256.land (UInt256.ofNat (2^244-1)) (inv*lo) :=
  mask_mul_mask lo inv 244 244 (by decide) (by decide)

theorem mask96_mul_mask244 (lo inv : UInt256) :
    UInt256.land (UInt256.ofNat 79228162514264337593543950335)
      (inv * UInt256.land (UInt256.ofNat (2^244-1)) lo) =
    UInt256.land (UInt256.ofNat 79228162514264337593543950335) (inv*lo) :=
  mask_mul_mask lo inv 244 96 (by decide) (by decide)

#print axioms mask_mul_mask
end HistoricalSearch.CRTMaskElision
