import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeContract
import Challenge.Modexp.Submission.Proofs.Cycle.SelectedRadix
set_option warningAsError true
set_option maxHeartbeats 3000000
namespace CycleSubmission.ControlArithmetic
open EvmSemantics
open Challenge.EvmProof.Word
open HistoricalSearch.MixedMontgomery
open CycleSubmission.Normalization

def value (a : Nat → UInt256) : Nat := weighted (2^240) 9 (fun i => (a i).toNat)
def overflowFlag (a : Nat → UInt256) : UInt256 :=
  UInt256.shiftRight (a 8) (UInt256.ofNat 240)
def normalized (a n : Nat → UInt256) : Nat → UInt256 :=
  if (overflowFlag a).toNat = 0 then a else CycleSubmission.NormalizeMeaning.output a n

theorem overflow_zero (a : Nat → UInt256)
    (ha : ∀ i < 8, (a i).toNat < 2^240) :
    (overflowFlag a).toNat = 0 ↔ value a < (2^240)^9 := by
  rw [overflowFlag, shiftRight_toNat _ (by decide : 240 < 256),
    Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
  have hlo := weightedBound (2^240) 8 (fun i => (a i).toNat) (Nat.two_pow_pos _) ha
  have h := CycleSubmission.Radix.overflowTest (2^240)
    (weighted (2^240) 8 (fun i => (a i).toNat)) (a 8).toNat (Nat.two_pow_pos _) hlo
  have hv : value a = weighted (2^240) 8 (fun i => (a i).toNat) + (2^240)^8*(a 8).toNat := by
    rw [value, weightedSucc]
    rw [Nat.mul_comm]
  rw [← hv] at h
  omega

theorem normalized_value (a n : Nat → UInt256)
    (ha : ∀ i < 8, (a i).toNat < 2^240)
    (hn : ∀ i < 9, (n i).toNat < 2^240)
    (hN : value n < (2^240)^9) :
    value (normalized a n) = HistoricalSearch.MixedMontgomery.normalize ((2^240)^9) (value n) (value a) := by
  by_cases hz : (overflowFlag a).toNat = 0
  · have h := (overflow_zero a ha).mp hz
    simp only [normalized, if_pos hz, HistoricalSearch.MixedMontgomery.normalize, if_neg (Nat.not_le.mpr h)]
  · have hover : (2^240)^9 ≤ value a := by
      have h := overflow_zero a ha
      omega
    have hv := CycleSubmission.NormalizeMeaning.output_value a n ha hn
      (Nat.le_trans (Nat.le_of_lt hN) hover)
    simp only [normalized, if_neg hz, HistoricalSearch.MixedMontgomery.normalize, if_pos hover]
    change value (CycleSubmission.NormalizeMeaning.output a n) + value n = value a at hv
    omega

theorem normalized_bounded (a n : Nat → UInt256)
    (ha : ∀ i < 8, (a i).toNat < 2^240)
    (hn : ∀ i < 9, (n i).toNat < 2^240)
    (hN : value n < (2^240)^9) (hupper : value a < (2^240)^9+value n) :
    ∀ i < 9, (normalized a n i).toNat < 2^240 := by
  by_cases hz : (overflowFlag a).toNat = 0
  · have hv := (overflow_zero a ha).mp hz
    intro i hi
    simp only [normalized, if_pos hz]
    by_cases he : i = 8
    · subst i
      exact CycleSubmission.NormalizeMeaning.top_digit_bounded (2^240) 8
        (fun j => (a j).toNat) (Nat.two_pow_pos _) hv
    · exact ha i (by omega)
  · have hover : (2^240)^9 ≤ value a := by
      have h := overflow_zero a ha
      omega
    simpa only [normalized, if_neg hz] using
      (CycleSubmission.NormalizeMeaning.overflow_contract a n ha hn hN hover hupper).2.1

end CycleSubmission.ControlArithmetic
