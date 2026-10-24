import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeMeaning
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 4096
namespace CycleSubmission.NormalizeMeaning
open EvmSemantics EvmSemantics.EVM
open HistoricalSearch.MixedMontgomery
open CycleSubmission.Normalization
theorem output_value (a n : Nat → UInt256)
    (ha : ∀ i < 8, (a i).toNat < 2^240)
    (hn : ∀ i < 9, (n i).toNat < 2^240)
    (horder : weighted (2^240) 9 (fun i => (n i).toNat) ≤
      weighted (2^240) 9 (fun i => (a i).toNat)) :
    weighted (2^240) 9 (fun i => (output a n i).toNat) +
      weighted (2^240) 9 (fun i => (n i).toNat) =
      weighted (2^240) 9 (fun i => (a i).toNat) := by
  have h := (nineWordSubtract a n ha hn horder).1
  rw [weightedSucc _ 8]
  have hlow : weighted (2^240) 8 (fun i => (output a n i).toNat) =
      weighted (2^240) 8 (fun i => (lowDigit a n i).toNat) := by
    apply Finset.sum_congr rfl
    intro i hi
    change (output a n i).toNat * (2^240)^i = (lowDigit a n i).toNat * (2^240)^i
    simp only [output, if_pos (Finset.mem_range.mp hi)]
  rw [hlow]
  simpa only [output, show ¬ (8 : Nat) < 8 by decide, if_false] using h

theorem output_low_bounded (a n : Nat → UInt256)
    (ha : ∀ i < 8, (a i).toNat < 2^240)
    (hn : ∀ i < 9, (n i).toNat < 2^240) :
    ∀ i < 8, (output a n i).toNat < 2^240 := by
  intro i hi
  rw [output, if_pos hi]
  exact (digitSubtract (a i) (n i) (borrow a n i)
    (ha i hi) (hn i (by omega)) (borrowBound a n i)).1

theorem top_digit_bounded (B k : Nat) (d : Nat → Nat) (hB : 0 < B)
    (h : weighted B (k+1) d < B^(k+1)) : d k < B := by
  rw [weightedSucc, Nat.pow_succ] at h
  have hp : 0 < B^k := Nat.pow_pos hB
  nlinarith

theorem subtractResidue (D N A : Nat) (h : D+N=A) : D%N = A%N := by
  have hm := congrArg (fun x => x % N) h
  simpa only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod] using hm

theorem overflow_contract (a n : Nat → UInt256)
    (ha : ∀ i < 8, (a i).toNat < 2^240)
    (hn : ∀ i < 9, (n i).toNat < 2^240)
    (hN : weighted (2^240) 9 (fun i => (n i).toNat) < (2^240)^9)
    (hover : (2^240)^9 ≤ weighted (2^240) 9 (fun i => (a i).toNat))
    (hupper : weighted (2^240) 9 (fun i => (a i).toNat) <
      (2^240)^9 + weighted (2^240) 9 (fun i => (n i).toNat)) :
    weighted (2^240) 9 (fun i => (output a n i).toNat) < (2^240)^9 ∧
    (∀ i < 9, (output a n i).toNat < 2^240) ∧
    weighted (2^240) 9 (fun i => (output a n i).toNat) %
        weighted (2^240) 9 (fun i => (n i).toNat) =
      weighted (2^240) 9 (fun i => (a i).toNat) %
        weighted (2^240) 9 (fun i => (n i).toNat) := by
  have hv := output_value a n ha hn (Nat.le_trans (Nat.le_of_lt hN) hover)
  have hu : weighted (2^240) 9 (fun i => (output a n i).toNat) +
      weighted (2^240) 9 (fun i => (n i).toNat) <
      (2^240)^9 + weighted (2^240) 9 (fun i => (n i).toNat) := by
    rw [hv]
    exact hupper
  have hnew := Nat.lt_of_add_lt_add_right hu
  refine ⟨hnew, ?_, ?_⟩
  · intro i hi
    by_cases he : i=8
    · subst i
      exact top_digit_bounded (2^240) 8 (fun j => (output a n j).toNat)
        (Nat.two_pow_pos _) hnew
    · exact output_low_bounded a n ha hn i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) he)
  · exact subtractResidue _ _ _ hv

end CycleSubmission.NormalizeMeaning
