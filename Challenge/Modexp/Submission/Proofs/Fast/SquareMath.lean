import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

set_option warningAsError true

/-!
# The squaring identity behind the square-by-entry CIOS rows

Row `r` of a square uses the multiplier `a2 r` = limb `r` of `2a` (with the top
bit of the previous limb carried in), adds the diagonal `a r * (a r + tbm r)` to
`t[r]`, and accumulates `a2 r * a j` into `t[j]` for `j > r`.  Summed over all
rows with their row weights `B ^ r`, these contributions are exactly `a ^ 2`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareMath

/-- `Σ_{k<j} f k * B ^ k`. -/
def lsum (B : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => lsum B f j + f j * B ^ j

/-- Top bit carried into limb `i` (the top bit of limb `i-1`; zero for `i = 0`). -/
def tbm (h : Nat) (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => a i / h

/-- Limb `i` of `2a` (radix `B = 2h`). -/
def a2 (h : Nat) (a : Nat → Nat) (i : Nat) : Nat := (2 * a i + tbm h a i) % (2 * h)

/-- The contribution of row `r` in its own frame: the diagonal at weight `B^r`
plus `a2 r` times the limbs above `r`. -/
def rowX (h n : Nat) (a : Nat → Nat) (r : Nat) : Nat :=
  a r * (a r + tbm h a r) * (2 * h) ^ r +
    a2 h a r * (lsum (2 * h) a n - lsum (2 * h) a (r + 1))

theorem lsum_mono (B : Nat) (f : Nat → Nat) : ∀ {i j : Nat}, i ≤ j → lsum B f i ≤ lsum B f j := by
  intro i j hij
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact le_trans (ih (by omega)) (by simp [lsum])
      · rw [show i = j + 1 by omega]

theorem tbm_le_one {h : Nat} (hh : 0 < h) (a : Nat → Nat) (ha : ∀ k, a k < 2 * h) (i : Nat) :
    tbm h a i ≤ 1 := by
  cases i with
  | zero => simp [tbm]
  | succ i =>
      simp only [tbm]
      have := ha i
      exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hh).2 (by omega))

/-- `2 a_i + tbm_i = a2_i + tbm_{i+1} * B`. -/
theorem a2_carry {h : Nat} (hh : 0 < h) (a : Nat → Nat) (ha : ∀ k, a k < 2 * h) (i : Nat) :
    2 * a i + tbm h a i = a2 h a i + tbm h a (i + 1) * (2 * h) := by
  have ht := tbm_le_one hh a ha i
  have hai := ha i
  have htb : tbm h a (i + 1) = a i / h := rfl
  rw [htb]; unfold a2
  have hd : (2 * a i + tbm h a i) / (2 * h) = a i / h := by
    rcases Nat.lt_or_ge (a i) h with hlt | hge
    · rw [Nat.div_eq_of_lt hlt, Nat.div_eq_of_lt (by omega)]
    · have h1 : a i / h = 1 := by
        apply Nat.le_antisymm
        · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hh).2 (by omega))
        · exact (Nat.le_div_iff_mul_le hh).2 (by omega)
      have h2 : (2 * a i + tbm h a i) / (2 * h) = 1 := by
        apply Nat.le_antisymm
        · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega))
        · exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      rw [h1, h2]
  have := Nat.mod_add_div (2 * a i + tbm h a i) (2 * h)
  rw [hd] at this
  linarith

/-- The row invariant: after rows `0..i-1`,
`Σ_{r<i} X_r B^r + tbm_i B^i U_i = L_i^2 + 2 L_i U_i`, `U_i = A - L_i`. -/
theorem rows_identity {h : Nat} (hh : 0 < h) (a : Nat → Nat) (ha : ∀ k, a k < 2 * h) (n : Nat) :
    ∀ i, i ≤ n →
      lsum (2 * h) (rowX h n a) i +
          tbm h a i * (2 * h) ^ i * (lsum (2 * h) a n - lsum (2 * h) a i) =
        lsum (2 * h) a i ^ 2 +
          2 * lsum (2 * h) a i * (lsum (2 * h) a n - lsum (2 * h) a i) := by
  intro i
  induction i with
  | zero => intro _; simp [lsum, tbm]
  | succ i ih =>
      intro hin
      have hih := ih (by omega)
      set B := 2 * h with hB
      set A := lsum B a n
      have hLi : lsum B a (i + 1) ≤ A := lsum_mono B a (by omega)
      set U := A - lsum B a (i + 1) with hU
      have hUi : A - lsum B a i = a i * B ^ i + U := by
        simp only [hU, lsum] at hLi ⊢; omega
      rw [hUi] at hih
      have hc := a2_carry hh a ha i
      rw [← hB] at hc
      have hstep : lsum B (rowX h n a) (i + 1) = lsum B (rowX h n a) i +
          (a i * (a i + tbm h a i) * B ^ i + a2 h a i * U) * B ^ i := rfl
      rw [hstep, show lsum B a (i + 1) = lsum B a i + a i * B ^ i from rfl]
      -- add `tbm_i B^i U_i` to both sides and use the invariant
      have key : (lsum B (rowX h n a) i + (a i * (a i + tbm h a i) * B ^ i + a2 h a i * U) * B ^ i +
            tbm h a (i + 1) * B ^ (i + 1) * U) + tbm h a i * B ^ i * (a i * B ^ i + U) =
          ((lsum B a i + a i * B ^ i) ^ 2 + 2 * (lsum B a i + a i * B ^ i) * U) +
            tbm h a i * B ^ i * (a i * B ^ i + U) := by
        have e1 : (lsum B (rowX h n a) i + (a i * (a i + tbm h a i) * B ^ i + a2 h a i * U) * B ^ i +
            tbm h a (i + 1) * B ^ (i + 1) * U) + tbm h a i * B ^ i * (a i * B ^ i + U) =
            (lsum B (rowX h n a) i + tbm h a i * B ^ i * (a i * B ^ i + U)) +
              (a i * (a i + tbm h a i) * B ^ i * B ^ i + (a2 h a i + tbm h a (i + 1) * B) * U * B ^ i) := by
          ring
        rw [e1, hih, ← hc]
        ring
      omega

/-- **The squaring identity**: the n rows contribute exactly `a ^ 2`. -/
theorem square_identity {h : Nat} (hh : 0 < h) (a : Nat → Nat) (ha : ∀ k, a k < 2 * h) (n : Nat) :
    lsum (2 * h) (rowX h n a) n = lsum (2 * h) a n ^ 2 := by
  have := rows_identity hh a ha n n le_rfl
  simpa using this

end Challenge.Modexp.Submission.Proofs.Fast.SquareMath
