import Challenge.Modexp.Submission.Proofs.CRT.MixedMontgomery
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace HistoricalSearch.SeventeenColumns
open scoped BigOperators
open HistoricalSearch.MixedMontgomery
open Challenge.Modexp.Submission.Proofs.Fast.Model

/-- Concrete columns 0 through 16, followed by zero. -/
def extend17 (f : Nat → Nat) (i : Nat) : Nat := if i < 17 then f i else 0

@[simp] theorem extend17_low (f : Nat → Nat) {i : Nat} (hi : i < 17) :
    extend17 f i = f i := by simp [extend17, hi]

@[simp] theorem extend17_high (f : Nat → Nat) {i : Nat} (hi : 17 ≤ i) :
    extend17 f i = 0 := by simp [extend17, Nat.not_lt.mpr hi]

theorem convolution17 (a b : Nat → Nat) : convolution 9 a b 17 = 0 := by
  unfold convolution
  apply Finset.sum_eq_zero
  intro ij hij
  have hh := Finset.mem_filter.mp hij
  have hi := Finset.mem_product.mp hh.1
  have ha := Finset.mem_range.mp hi.1
  have hb := Finset.mem_range.mp hi.2
  omega

/-- A column only observes cancellation digits whose index is at most t. -/
theorem convolution_prefix (k t : Nat) (q q' n : Nat → Nat)
    (h : ∀ i < k, i ≤ t → q i = q' i) :
    convolution k q n t = convolution k q' n t := by
  unfold convolution
  apply Finset.sum_congr rfl
  intro ij hij
  have hh := Finset.mem_filter.mp hij
  have hi := Finset.mem_product.mp hh.1
  rw [h ij.1 (Finset.mem_range.mp hi.1) (by omega)]

/-- The ordinary top-cell sum discharges the omitted radix-carry row. -/
theorem recurrence18 (beta : Nat) (a q m d c : Nat → Nat)
    (hrec : ∀ i < 16, d i + beta * c (i+1) =
      convolution 9 a a i + convolution 9 q m i + c i)
    (htail : d 16 = convolution 9 a a 16 + convolution 9 q m 16 + c 16) :
    ∀ i < 18, extend17 d i + beta * extend17 c (i+1) =
      convolution 9 a a i + convolution 9 q m i + extend17 c i := by
  intro i hi
  by_cases h : i < 16
  · simpa only [extend17_low d (by omega : i < 17),
      extend17_low c (by omega : i+1 < 17), extend17_low c (by omega : i < 17)]
      using hrec i h
  · have he : i = 16 ∨ i = 17 := by omega
    rcases he with rfl | rfl
    · simpa [extend17] using htail
    · simp [extend17, convolution17]

/-- Nine stored high digits equal the generic high block. -/
theorem highBlock17 (beta : Nat) (d c : Nat → Nat) :
    highBlock beta (extend17 d) (extend17 c) =
      weighted beta 9 (fun i => d (8+i)) := by
  unfold highBlock
  rw [extend17_high c (by decide : 17 ≤ 18)]
  simp only [Nat.mul_zero, Nat.add_zero]
  unfold weighted
  rw [show 10 = 9+1 from rfl, Finset.sum_range_succ]
  simp only [show 8+9 = 17 from rfl, extend17_high d (by decide : 17 ≤ 17),
    Nat.zero_mul, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [extend17_low d (by have := Finset.mem_range.mp hi; omega)]

/-- Exact identity for sixteen CRT rows plus the ordinary tail. -/
theorem exact17 (beta F R : Nat) (a q m d c : Nat → Nat)
    (hF : F ∣ beta) (hR : R = beta^8*F)
    (hc : c 0 = 0) (hzero : ∀ i < 8, d i = 0) (hlast : d 8 % F = 0)
    (hrec : ∀ i < 16, d i + beta * c (i+1) =
      convolution 9 a a i + convolution 9 q m i + c i)
    (htail : d 16 = convolution 9 a a 16 + convolution 9 q m 16 + c 16) :
    (weighted beta 9 (fun i => d (8+i)) / F) * R =
      weighted beta 9 a * weighted beta 9 a + weighted beta 9 q * weighted beta 9 m := by
  have h := mixedExact beta F R a a q m (extend17 d) (extend17 c) hF hR
    (by simpa [extend17] using hc)
    (fun i hi => by rw [extend17_low d (by omega)]; exact hzero i hi)
    (by simpa [extend17] using hlast)
    (recurrence18 beta a q m d c hrec htail)
  simpa only [highBlock17] using h

/-- Complete square arithmetic; the caller supplies concrete memory facts. -/
theorem contract17 (beta F R : Nat) (a q m d c : Nat → Nat)
    (hbeta : 0 < beta) (hFpos : 0 < F) (hF : F ∣ beta) (hR : R = beta^8*F)
    (hc : c 0 = 0) (hzero : ∀ i < 8, d i = 0) (hlast : d 8 % F = 0)
    (hrec : ∀ i < 16, d i + beta * c (i+1) =
      convolution 9 a a i + convolution 9 q m i + c i)
    (htail : d 16 = convolution 9 a a 16 + convolution 9 q m 16 + c 16)
    (hqlow : ∀ i < 8, q i < beta) (hqhigh : q 8 < F)
    (hA : weighted beta 9 a < R)
    (hN : 0 < weighted beta 9 m) (hNR : weighted beta 9 m < R)
    (hcop : Nat.Coprime R (weighted beta 9 m)) :
    normalize R (weighted beta 9 m) (weighted beta 9 (fun i => d (8+i)) / F) < R ∧
    normalize R (weighted beta 9 m) (weighted beta 9 (fun i => d (8+i)) / F) %
      weighted beta 9 m = montMul (weighted beta 9 m) R (weighted beta 9 a) (weighted beta 9 a) := by
  apply arithmeticContract R (weighted beta 9 m) (weighted beta 9 a)
    (weighted beta 9 a) (weighted beta 9 q) _
    (by rw [hR]; exact Nat.mul_pos (Nat.pow_pos hbeta) hFpos) hN hNR hA hA
    (by rw [hR]; exact mixedCancellationBound beta F q hbeta hqlow hqhigh) hcop
  exact exact17 beta F R a q m d c hF hR hc hzero hlast hrec htail

#print axioms convolution_prefix
#print axioms exact17
#print axioms contract17
end HistoricalSearch.SeventeenColumns
