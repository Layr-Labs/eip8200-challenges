import Challenge.Modexp.Submission.Proofs.R5.SquareMeaning
import Challenge.Modexp.Submission.Proofs.R5.LoopRun
import Challenge.Modexp.Submission.Proofs.R5.RouteMath
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000
set_option exponentiation.threshold 4096

/-!
# The r5 square loop (meaning)

One square of digits `x` (all below `2^240`, value `X` with `X + 2N ≤ R`) gives digits `z`
(again below `2^240`) with `Z * R = X * X + Q * N`, `Q < R`, and `Z + 2N ≤ R`.
-/

namespace CycleSubmission.R5.LoopMeaning
open EvmSemantics
open HistoricalSearch.MixedMontgomery
open CycleSubmission.WordArithmetic
open CycleSubmission.R5.SquareRun CycleSubmission.R5.SquareMeaning CycleSubmission.R5.LoopRun

def val (x : D5) : Nat :=
  x.d0.toNat + x.d1.toNat * radix + x.d2.toNat * radix^2 + x.d3.toNat * radix^3 + x.d4.toNat * radix^4

def ok (x : D5) : Prop :=
  x.d0.toNat < radix ∧ x.d1.toNat < radix ∧ x.d2.toNat < radix ∧ x.d3.toNat < radix ∧ x.d4.toNat < radix

theorem radix_pow5 : radix^5 = RouteMath.R := by norm_num [radix, RouteMath.R]

/-- Five digits below the radix have value below `R`. -/
theorem bound5 (a0 a1 a2 a3 a4 : Nat) (h0 : a0 < radix) (h1 : a1 < radix) (h2 : a2 < radix)
    (h3 : a3 < radix) (h4 : a4 < radix) :
    a0 + a1 * radix + a2 * radix^2 + a3 * radix^3 + a4 * radix^4 < RouteMath.R := by
  rw [← radix_pow5]
  have s1 : (a1 + 1) * radix ≤ radix * radix := Nat.mul_le_mul_right _ h1
  have s2 : (a2 + 1) * radix^2 ≤ radix * radix^2 := Nat.mul_le_mul_right _ h2
  have s3 : (a3 + 1) * radix^3 ≤ radix * radix^3 := Nat.mul_le_mul_right _ h3
  have s4 : (a4 + 1) * radix^4 ≤ radix * radix^4 := Nat.mul_le_mul_right _ h4
  linarith

theorem val_lt (x : D5) (h : ok x) : val x < RouteMath.R := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact bound5 _ _ _ _ _ h0 h1 h2 h3 h4

theorem top_lt (z : D5) (h0 : z.d0.toNat < radix) (h1 : z.d1.toNat < radix) (h2 : z.d2.toNat < radix)
    (h3 : z.d3.toNat < radix) (hz : val z < RouteMath.R) : z.d4.toNat < radix := by
  rcases Nat.lt_or_ge z.d4.toNat radix with h | h
  · exact h
  exfalso
  rw [← radix_pow5] at hz
  unfold val at hz
  have : radix^5 ≤ z.d4.toNat * radix^4 := by
    rw [show radix^5 = radix * radix^4 by ring]; exact Nat.mul_le_mul_right _ h
  omega

section
variable (n0 n1 n2 n3 n4 P inv ninv : UInt256) (N : Nat)
  (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
  (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
  (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0)
  (hNval : N = val ⟨n0, n1, n2, n3, n4⟩)
include hinv hP hn1 hn2 hn3 hn4 hn0 hN hNval

theorem step (x : D5) (c : UInt256) (hx : ok x) (h4 : 4*N ≤ RouteMath.R) (hNpos : 0 < N)
    (hb : val x + 2*N ≤ RouteMath.R) :
    ok (next n1 n2 n3 n4 P inv n0 x c) ∧ val (next n1 n2 n3 n4 P inv n0 x c) + 2*N ≤ RouteMath.R ∧
    ∃ Q, Q < RouteMath.R ∧ val (next n1 n2 n3 n4 P inv n0 x c) * RouteMath.R = val x * val x + Q * N := by
  obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hq, hz, heq⟩ := sq_exact x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv c n0 ninv N hinv hP
    hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hn0 hN
  simp only [weighted, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, pow_zero,
    pow_one, mul_one, sqDd, sqXd, sqYd, sqNd] at heq
  have hQ : weighted radix 5 (sqQd x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv c n0) < RouteMath.R := by
    simp only [weighted, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, pow_zero,
      pow_one, mul_one]
    exact bound5 _ _ _ _ _ (hq 0 (by decide)) (hq 1 (by decide)) (hq 2 (by decide))
      (hq 3 (by decide)) (hq 4 (by decide))
  have hexact : val (next n1 n2 n3 n4 P inv n0 x c) * RouteMath.R = val x * val x +
      weighted radix 5 (sqQd x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv c n0) * N := by
    rw [← radix_pow5, hNval]
    simp only [val, next, weighted, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add,
      pow_zero, pow_one, mul_one]
    linarith [heq]
  have hlow0 := hz 0 (by decide); have hlow1 := hz 1 (by decide)
  have hlow2 := hz 2 (by decide); have hlow3 := hz 3 (by decide)
  simp only [sqDd] at hlow0 hlow1 hlow2 hlow3
  have hbound : val (next n1 n2 n3 n4 P inv n0 x c) ≤ RouteMath.R - 2*N :=
    RouteMath.square_bound N RouteMath.R (RouteMath.R - 2*N) (val x) _ _ (by omega) h4
      (by norm_num [RouteMath.R]) (by omega) hQ hexact
  refine ⟨⟨hlow0, hlow1, hlow2, hlow3, ?_⟩, by omega, _, hQ, hexact⟩
  apply top_lt (next n1 n2 n3 n4 P inv n0 x c) hlow0 hlow1 hlow2 hlow3
  omega
end

end CycleSubmission.R5.LoopMeaning
