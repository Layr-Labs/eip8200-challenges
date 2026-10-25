import Challenge.Modexp.Submission.Proofs.Cycle.ControlArithmetic
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
namespace CycleSubmission.CompareArithmetic
open EvmSemantics HistoricalSearch.MixedMontgomery
open CycleSubmission.Normalization
attribute [local instance] Classical.propDecidable
open CycleSubmission.ControlArithmetic (value)

def less (a n : Nat → UInt256) : Nat → Prop
  | 0 => False
  | k+1 => (a k).toNat < (n k).toNat ∨ ((a k).toNat = (n k).toNat ∧ less a n k)

theorem weighted_compare (B k : Nat) (a n : Nat → Nat) (hB : 0 < B)
    (ha : ∀ i < k, a i < B) (hn : ∀ i < k, n i < B) :
    weighted B (k+1) a < weighted B (k+1) n ↔
      a k < n k ∨ (a k = n k ∧ weighted B k a < weighted B k n) := by
  have hA := weightedBound B k a hB ha
  have hN := weightedBound B k n hB hn
  have hp : 0 < B^k := Nat.pow_pos hB
  rw [weightedSucc, weightedSucc]
  constructor
  · intro h
    by_cases he : a k = n k
    · right; constructor
      · exact he
      · rw [he] at h; omega
    · left
      by_contra hge
      have : n k + 1 ≤ a k := by omega
      nlinarith
  · rintro (h | ⟨h, hl⟩)
    · have : a k + 1 ≤ n k := by omega
      nlinarith
    · rw [h]; omega

theorem less_iff (a n : Nat → UInt256) (k : Nat) (hk : k ≤ 9)
    (ha : ∀ i < 8, (a i).toNat < 2^240)
    (hn : ∀ i < 8, (n i).toNat < 2^240) :
    less a n k ↔ weighted (2^240) k (fun i => (a i).toNat) <
      weighted (2^240) k (fun i => (n i).toNat) := by
  induction k with
  | zero => simp [less, weighted]
  | succ k ih =>
    rw [weighted_compare (2^240) k _ _ (Nat.two_pow_pos _)
      (fun i hi => ha i (by omega)) (fun i hi => hn i (by omega))]
    simp only [less, ih (by omega)]

def destination (a n : Nat → UInt256) : Nat → Nat
  | 0 => 10399
  | k+1 => if (a k).toNat < (n k).toNat then 10409
    else if (n k).toNat < (a k).toNat then 10399 else destination a n k

theorem destination_eq (a n : Nat → UInt256) (k : Nat) :
    destination a n k = if less a n k then 10409 else 10399 := by
  induction k with
  | zero => simp [destination, less]
  | succ k ih =>
    by_cases hl : (a k).toNat < (n k).toNat
    · simp [destination, less, hl]
    · by_cases hg : (n k).toNat < (a k).toNat
      · have he : ¬ (a k).toNat = (n k).toNat := by omega
        simp [destination, less, hl, hg, he]
      · have he : (a k).toNat = (n k).toNat := by omega
        simp [destination, less, hl, hg, he, ih]

theorem final_destination (a n : Nat → UInt256)
    (ha : ∀ i < 8, (a i).toNat < 2^240)
    (hn : ∀ i < 8, (n i).toNat < 2^240) :
    destination a n 9 = if value a < value n then 10409 else 10399 := by
  rw [destination_eq, less_iff a n 9 (by decide) ha hn]
  by_cases h : value a < value n
  · have hw : weighted (2^240) 9 (fun i => (a i).toNat) < weighted (2^240) 9 (fun i => (n i).toNat) := h
    simp only [if_pos h, if_pos hw]
  · have hw : ¬ weighted (2^240) 9 (fun i => (a i).toNat) < weighted (2^240) 9 (fun i => (n i).toNat) := h
    simp only [if_neg h, if_neg hw]

end CycleSubmission.CompareArithmetic
