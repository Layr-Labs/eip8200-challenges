import Challenge.Modexp.Submission.Proofs.CRT.MixedMontgomery
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace CycleSubmission.Convolution
open HistoricalSearch.MixedMontgomery

theorem column0 (a b : Nat → Nat) : convolution 9 a b 0 = a 0 * b 0 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 0) = {(0, 0)} by decide]
  simp <;> omega

theorem column1 (a b : Nat → Nat) : convolution 9 a b 1 = a 0 * b 1 + a 1 * b 0 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 1) = {(0, 1), (1, 0)} by decide]
  simp <;> omega

theorem column2 (a b : Nat → Nat) : convolution 9 a b 2 = a 0 * b 2 + a 1 * b 1 + a 2 * b 0 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 2) = {(0, 2), (1, 1), (2, 0)} by decide]
  simp <;> omega

theorem column3 (a b : Nat → Nat) : convolution 9 a b 3 = a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 3) = {(0, 3), (1, 2), (2, 1), (3, 0)} by decide]
  simp <;> omega

theorem column4 (a b : Nat → Nat) : convolution 9 a b 4 = a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 4) = {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} by decide]
  simp <;> omega

theorem column5 (a b : Nat → Nat) : convolution 9 a b 5 = a 0 * b 5 + a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1 + a 5 * b 0 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 5) = {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} by decide]
  simp <;> omega

theorem column6 (a b : Nat → Nat) : convolution 9 a b 6 = a 0 * b 6 + a 1 * b 5 + a 2 * b 4 + a 3 * b 3 + a 4 * b 2 + a 5 * b 1 + a 6 * b 0 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 6) = {(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (6, 0)} by decide]
  simp <;> omega

theorem column7 (a b : Nat → Nat) : convolution 9 a b 7 = a 0 * b 7 + a 1 * b 6 + a 2 * b 5 + a 3 * b 4 + a 4 * b 3 + a 5 * b 2 + a 6 * b 1 + a 7 * b 0 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 7) = {(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1), (7, 0)} by decide]
  simp <;> omega

theorem column8 (a b : Nat → Nat) : convolution 9 a b 8 = a 0 * b 8 + a 1 * b 7 + a 2 * b 6 + a 3 * b 5 + a 4 * b 4 + a 5 * b 3 + a 6 * b 2 + a 7 * b 1 + a 8 * b 0 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 8) = {(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2), (7, 1), (8, 0)} by decide]
  simp <;> omega

theorem column9 (a b : Nat → Nat) : convolution 9 a b 9 = a 1 * b 8 + a 2 * b 7 + a 3 * b 6 + a 4 * b 5 + a 5 * b 4 + a 6 * b 3 + a 7 * b 2 + a 8 * b 1 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 9) = {(1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3), (7, 2), (8, 1)} by decide]
  simp <;> omega

theorem column10 (a b : Nat → Nat) : convolution 9 a b 10 = a 2 * b 8 + a 3 * b 7 + a 4 * b 6 + a 5 * b 5 + a 6 * b 4 + a 7 * b 3 + a 8 * b 2 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 10) = {(2, 8), (3, 7), (4, 6), (5, 5), (6, 4), (7, 3), (8, 2)} by decide]
  simp <;> omega

theorem column11 (a b : Nat → Nat) : convolution 9 a b 11 = a 3 * b 8 + a 4 * b 7 + a 5 * b 6 + a 6 * b 5 + a 7 * b 4 + a 8 * b 3 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 11) = {(3, 8), (4, 7), (5, 6), (6, 5), (7, 4), (8, 3)} by decide]
  simp <;> omega

theorem column12 (a b : Nat → Nat) : convolution 9 a b 12 = a 4 * b 8 + a 5 * b 7 + a 6 * b 6 + a 7 * b 5 + a 8 * b 4 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 12) = {(4, 8), (5, 7), (6, 6), (7, 5), (8, 4)} by decide]
  simp <;> omega

theorem column13 (a b : Nat → Nat) : convolution 9 a b 13 = a 5 * b 8 + a 6 * b 7 + a 7 * b 6 + a 8 * b 5 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 13) = {(5, 8), (6, 7), (7, 6), (8, 5)} by decide]
  simp <;> omega

theorem column14 (a b : Nat → Nat) : convolution 9 a b 14 = a 6 * b 8 + a 7 * b 7 + a 8 * b 6 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 14) = {(6, 8), (7, 7), (8, 6)} by decide]
  simp <;> omega

theorem column15 (a b : Nat → Nat) : convolution 9 a b 15 = a 7 * b 8 + a 8 * b 7 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 15) = {(7, 8), (8, 7)} by decide]
  simp <;> omega

theorem column16 (a b : Nat → Nat) : convolution 9 a b 16 = a 8 * b 8 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 16) = {(8, 8)} by decide]
  simp <;> omega

theorem column17 (a b : Nat → Nat) : convolution 9 a b 17 = 0 := by
  unfold convolution
  rw [show (Finset.range 9 ×ˢ Finset.range 9).filter (fun ij => ij.1 + ij.2 = 17) = ∅ by decide]
  simp <;> omega

end CycleSubmission.Convolution
