import Challenge.Modexp.Submission.Proofs.CRT.ProductAccumulate
import Challenge.Modexp.Submission.Proofs.CRT.MixedMontgomery
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace HistoricalSearch.WordCancellation
open EvmSemantics
open Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.ProductAccumulate
open HistoricalSearch.MixedMontgomery

def maskedDigit (lo inv : UInt256) (W F : Nat) : UInt256 :=
  ((lo &&& UInt256.ofNat (2^W-1))*inv) &&& UInt256.ofNat (2^F-1)

theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply word_ext
  rw [word_toNat_land, word_toNat_land, Nat.and_comm]

theorem mul_comm (a b : UInt256) : a*b = b*a := by
  apply word_ext
  rw [mul_toNat, mul_toNat, Nat.mul_comm]

theorem maskedDigit_commute (lo inv : UInt256) (W F : Nat) :
    UInt256.land (UInt256.ofNat (2^F-1))
      (inv*UInt256.land (UInt256.ofNat (2^W-1)) lo) = maskedDigit lo inv W F := by
  unfold maskedDigit
  rw [land_comm (UInt256.ofNat (2^F-1)), mul_comm inv, land_comm (UInt256.ofNat (2^W-1))]
  rfl

theorem mask_toNat (a : UInt256) (W : Nat) (hW : W ≤ 256) :
    (a &&& UInt256.ofNat (2^W-1)).toNat = a.toNat % 2^W := by
  have hp : (2^W : Nat) ≤ 2^256 := Nat.pow_le_pow_right (by decide) hW
  have hmask : 2^W-1 < (2^256 : Nat) := by have := Nat.two_pow_pos W; omega
  change (UInt256.land a (UInt256.ofNat (2^W-1))).toNat = _
  rw [word_toNat_land, word_toNat_ofNat, Nat.mod_eq_of_lt hmask, Nat.and_two_pow_sub_one_eq_mod]

theorem leftMask_lt (a : UInt256) (W : Nat) (hW : W ≤ 256) :
    (UInt256.land (UInt256.ofNat (2^W-1)) a).toNat < 2^W := by
  rw [land_comm]
  change (a &&& UInt256.ofNat (2^W-1)).toNat < _
  rw [mask_toNat a W hW]
  exact Nat.mod_lt _ (Nat.two_pow_pos W)

/-- The actual masked wrapped multiply computes the mathematical cancellation
digit modulo F, even though its intermediate product may overflow an EVM word. -/
theorem maskedDigit_toNat (lo inv : UInt256) (W F S : Nat)
    (hFW : F ≤ W) (hW : W ≤ 256) (hlo : lo.toNat = S % wordRadix) :
    (maskedDigit lo inv W F).toNat = (S*inv.toNat) % 2^F := by
  have hF : F ≤ 256 := hFW.trans hW
  have hdFW : (2^F : Nat) ∣ 2^W := Nat.pow_dvd_pow 2 hFW
  have hdFR : (2^F : Nat) ∣ 2^256 := Nat.pow_dvd_pow 2 hF
  unfold maskedDigit
  rw [mask_toNat _ F hF, mul_toNat, mask_toNat _ W hW,
    Nat.mod_mod_of_dvd _ hdFR, Nat.mul_mod, Nat.mod_mod_of_dvd _ hdFW, hlo]
  change ((S % 2^256) % 2^F * (inv.toNat % 2^F)) % 2^F = _
  rw [Nat.mod_mod_of_dvd _ hdFR, ← Nat.mul_mod]

/-- The old 256-bit negative inverse also cancels modulo every smaller power
of two, and the modulus low limb has the same residue at that smaller radix. -/
theorem inverseAtWidth (N n0 inv W F : Nat) (hFW : F ≤ W) (hW : W ≤ 256)
    (hn0 : n0 = N % 2^W) (hinv : (N*inv+1) % 2^256 = 0) :
    (n0*inv+1) % 2^F = 0 := by
  have hdFW : (2^F : Nat) ∣ 2^W := Nat.pow_dvd_pow 2 hFW
  have hdFR : (2^F : Nat) ∣ 2^256 := Nat.pow_dvd_pow 2 (hFW.trans hW)
  have hi := congrArg (fun x => x % 2^F) hinv
  rw [Nat.mod_mod_of_dvd _ hdFR, Nat.zero_mod] at hi
  rw [hn0, Nat.add_mod, Nat.mul_mod, Nat.mod_mod_of_dvd _ hdFW,
    ← Nat.mul_mod, ← Nat.add_mod]
  exact hi

/-- Range and low-digit cancellation for the exact UInt256 digit expression. -/
theorem maskedDigitCancels (lo inv : UInt256) (W F S N n0 : Nat)
    (hFW : F ≤ W) (hW : W ≤ 256) (hlo : lo.toNat = S % wordRadix)
    (hn0 : n0 = N % 2^W) (hinv : (N*inv.toNat+1) % 2^256 = 0) :
    (maskedDigit lo inv W F).toNat < 2^F ∧
    (S+(maskedDigit lo inv W F).toNat*n0) % 2^F = 0 ∧
    ((S+(maskedDigit lo inv W F).toNat*n0) % 2^W) % 2^F = 0 := by
  rw [maskedDigit_toNat lo inv W F S hFW hW hlo]
  have hi := inverseAtWidth N n0 inv.toNat W F hFW hW hn0 hinv
  have hc := cancellationDigit (2^F) S n0 inv.toNat hi
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos F), hc, ?_⟩
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hFW)]
  exact hc

theorem fullDigitZero (lo inv : UInt256) (W S N n0 : Nat)
    (hW : W ≤ 256) (hlo : lo.toNat = S % wordRadix)
    (hn0 : n0 = N % 2^W) (hinv : (N*inv.toNat+1) % 2^256 = 0) :
    (S+(maskedDigit lo inv W W).toNat*n0) % 2^W = 0 :=
  (maskedDigitCancels lo inv W W S N n0 (by omega) hW hlo hn0 hinv).2.1


end HistoricalSearch.WordCancellation
