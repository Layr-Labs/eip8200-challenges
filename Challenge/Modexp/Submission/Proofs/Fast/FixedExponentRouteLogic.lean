import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute

set_option warningAsError true

/-!
# Semantic classification for the fixed-exponent route

This module keeps the calldata classification independent of concrete program
locations.  The located dispatcher proof can use these equivalences without
unfolding the eventual execution trace.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRouteLogic

open FixedExponentRoute

theorem matches_iff (input : ByteArray) (bsize esize : Nat) :
    Matches input bsize esize ↔
      (esize = 3 ∧ exponentValue input bsize esize = 65537) := by
  constructor
  · rintro ⟨count, hcase⟩
    cases hcase with
    | fermat hesize hvalue => exact ⟨hesize, hvalue⟩
  · rintro hfermat
    exact ⟨16, Case.fermat hfermat.1 hfermat.2⟩

theorem case_count_unique {input : ByteArray} {bsize esize a b : Nat}
    (ha : Case input bsize esize a) (hb : Case input bsize esize b) : a = b := by
  cases ha
  cases hb
  simp_all

theorem case_count_bounds {input : ByteArray} {bsize esize count : Nat}
    (hcase : Case input bsize esize count) : 1 ≤ count ∧ count ≤ 16 := by
  cases hcase
  omega

theorem not_matches_of_size {input : ByteArray} {bsize esize : Nat}
    (hne3 : esize ≠ 3) :
    ¬ Matches input bsize esize := by
  rw [matches_iff]
  aesop

theorem matches_three_iff (input : ByteArray) (bsize : Nat) :
    Matches input bsize 3 ↔ exponentValue input bsize 3 = 65537 := by
  rw [matches_iff]
  simp

end Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRouteLogic
