import Challenge.Modexp.Submission.Proofs.CRT.MixedMontgomery
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Five-digit Montgomery columns

`convolution 5` column forms and the exact equation of a five-digit kernel trace
(`montgomeryColumns` at 5 digits; the shape of `SelectedRadix.alignedExact` at 9).
-/

namespace CycleSubmission.R5.Kernel5
open HistoricalSearch.MixedMontgomery

theorem column0 (a b : Nat → Nat) : convolution 5 a b 0 = a 0 * b 0 := by
  unfold convolution
  rw [show (Finset.range 5 ×ˢ Finset.range 5).filter (fun ij => ij.1 + ij.2 = 0) = {(0, 0)} by decide]
  simp <;> omega

theorem column1 (a b : Nat → Nat) : convolution 5 a b 1 = a 0 * b 1 + a 1 * b 0 := by
  unfold convolution
  rw [show (Finset.range 5 ×ˢ Finset.range 5).filter (fun ij => ij.1 + ij.2 = 1) = {(0, 1), (1, 0)} by decide]
  simp <;> omega

theorem column2 (a b : Nat → Nat) : convolution 5 a b 2 = a 0 * b 2 + a 1 * b 1 + a 2 * b 0 := by
  unfold convolution
  rw [show (Finset.range 5 ×ˢ Finset.range 5).filter (fun ij => ij.1 + ij.2 = 2) = {(0, 2), (1, 1), (2, 0)} by decide]
  simp <;> omega

theorem column3 (a b : Nat → Nat) : convolution 5 a b 3 = a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0 := by
  unfold convolution
  rw [show (Finset.range 5 ×ˢ Finset.range 5).filter (fun ij => ij.1 + ij.2 = 3) = {(0, 3), (1, 2), (2, 1), (3, 0)} by decide]
  simp <;> omega

theorem column4 (a b : Nat → Nat) : convolution 5 a b 4 = a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0 := by
  unfold convolution
  rw [show (Finset.range 5 ×ˢ Finset.range 5).filter (fun ij => ij.1 + ij.2 = 4) = {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} by decide]
  simp <;> omega

theorem column5 (a b : Nat → Nat) : convolution 5 a b 5 = a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1 := by
  unfold convolution
  rw [show (Finset.range 5 ×ˢ Finset.range 5).filter (fun ij => ij.1 + ij.2 = 5) = {(1, 4), (2, 3), (3, 2), (4, 1)} by decide]
  simp <;> omega

theorem column6 (a b : Nat → Nat) : convolution 5 a b 6 = a 2 * b 4 + a 3 * b 3 + a 4 * b 2 := by
  unfold convolution
  rw [show (Finset.range 5 ×ˢ Finset.range 5).filter (fun ij => ij.1 + ij.2 = 6) = {(2, 4), (3, 3), (4, 2)} by decide]
  simp <;> omega

theorem column7 (a b : Nat → Nat) : convolution 5 a b 7 = a 3 * b 4 + a 4 * b 3 := by
  unfold convolution
  rw [show (Finset.range 5 ×ˢ Finset.range 5).filter (fun ij => ij.1 + ij.2 = 7) = {(3, 4), (4, 3)} by decide]
  simp <;> omega

theorem column8 (a b : Nat → Nat) : convolution 5 a b 8 = a 4 * b 4 := by
  unfold convolution
  rw [show (Finset.range 5 ×ˢ Finset.range 5).filter (fun ij => ij.1 + ij.2 = 8) = {(4, 4)} by decide]
  simp <;> omega

theorem column9 (a b : Nat → Nat) : convolution 5 a b 9 = 0 := by
  unfold convolution
  rw [show (Finset.range 5 ×ˢ Finset.range 5).filter (fun ij => ij.1 + ij.2 = 9) = ∅ by decide]
  simp <;> omega

theorem exact5 (beta : Nat) (a b q m d c : Nat → Nat)
    (hc : c 0 = 0) (hfinal : c 10 = 0)
    (hzero : ∀ i < 5, d i = 0)
    (hrec : ∀ i < 10, d i + beta*c (i+1) =
      convolution 5 a b i + convolution 5 q m i + c i) :
    weighted beta 5 (fun i => d (5+i)) * beta^5 =
      weighted beta 5 a * weighted beta 5 b + weighted beta 5 q * weighted beta 5 m := by
  have h := montgomeryColumns beta 5 a b q m d c hc hrec
  have hs := weightedShift beta 5 5 d hzero
  change weighted beta 10 d = _ at hs
  change weighted beta 10 d + beta^10*c 10 = _ at h
  rw [hfinal, Nat.mul_zero, Nat.add_zero, hs] at h
  simpa only [Nat.mul_comm] using h

/-- The weighted value of five digits. -/
theorem weighted5 (beta : Nat) (f : Nat → Nat) :
    weighted beta 5 f = f 0 + f 1 * beta + f 2 * beta^2 + f 3 * beta^3 + f 4 * beta^4 := by
  simp [weighted, Finset.sum_range_succ]

end CycleSubmission.R5.Kernel5
