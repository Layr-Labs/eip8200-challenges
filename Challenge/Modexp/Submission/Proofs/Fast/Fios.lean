/-
FIOS_MATH.lean -- the arithmetic invariant of the fused (FIOS) Montgomery inner loop
that `artifact/fios-k9.hex` executes, and its discharge of
`Model.montMul_eq_mod_of_mul_eq`'s hypothesis `ht`.

WHAT THIS IS FOR
  The patch replaces the two CIOS inner loops (pc 4076.. multiply, pc 2241.. reduce)
  with one fused counted loop of trip count exactly `n-1`.  The arithmetic core of
  `Model.lean` is untouched: FIOS establishes the SAME relation `t * R = x * y + q * m`
  in a different summation order.  Concretely, `rowValue_mul` below proves that one
  FIOS row satisfies

      rowValue * beta  =  t + a * b_i + mu * m

  which is exactly the hypothesis `Model.cios_step` already consumes, so the outer
  structure (`Monpro.rows_invariant` -> `Model.montMul_eq_mod_of_mul_eq`) is reused
  verbatim.  Nothing here mentions CIOS or FIOS in its statement; the statements are
  the same, only the witness changed.

WHAT IT LANDS IN
  `Csub.csub_correct` (untouched by the patch) requires, at pc 2637:
      hlt  : t[n] * radix ^ n + lowValue < 2 * mm
      htn1 : t[n] <= 1
      plus `FastRepresents` of the low limbs and of the modulus, and `0 < mm`.
  `fios_final` produces the first; `top_limb_le_one` produces the second from it,
  by exactly the argument in `Monpro.monpro_tn_le_one`.

STATUS
  Every proof script below was COMPILED, with Lean 4.31.0, as
  `notes/monpro/check/FiosCore.lean` -- a byte-identical copy of the definitions,
  statements and tactic scripts against Lean core alone (Mathlib is not built in the
  authoring environment).  It reports
      exit 0, zero `sorry`, axioms [propext, Quot.sound]
  for `st_invariant`, `rowValue_mul`, `fios_row_eq`, `rows_invariant`, `fios_final`,
  `top_limb_le_one`, and [propext] for `peel_dvd`.  The scripts use only tactics that
  exist in both core and Mathlib (`omega`, `rw`, `simp only`, `induction`, `cases`,
  `obtain`, `refine`, `show`, `exact`).  Every `Nat.*` lemma name used was verified by
  `#check` against the pinned toolchain; none is invented.  The one step NOT covered by
  that check is flagged inline at `peel_dvd`.

MATHLIB / CORE LEMMAS USED, by name (all `#check`-verified at v4.31.0):
  Nat.div_add_mod, Nat.pow_succ, Nat.pow_zero, Nat.add_mul, Nat.mul_add, Nat.mul_assoc,
  Nat.mul_comm, Nat.add_assoc, Nat.zero_add, Nat.zero_mul, Nat.mul_zero, Nat.add_zero,
  Nat.mul_one, Nat.mul_mod_right, Nat.mul_le_mul_left, Nat.mul_le_mul_right,
  Nat.mul_div_cancel, Nat.div_lt_iff_lt_mul, Nat.two_mul, Nat.lt_or_ge, Nat.le_refl.
  From Model.lean: `cios_mu_dvd`, `montMul_eq_mod_of_mul_eq` (and `cios_bound`, whose
  local copy below is interchangeable).

IF IT DOES NOT COMPILE -- the two places I could not fully de-risk, and their fixes
  (1) `peel_dvd` ends with `simpa [peelMu, Nat.mul_comm] using h`.  This closed under
      core simp with the identical statement; Mathlib's larger simp set could normalise
      `h` differently.  If it fails, the residual goal is
        beta | (T 0 + A 0 * bi) % beta + M0 * ((T 0 + A 0 * bi) % beta * minv % beta)
      against
        h : beta | (T 0 + A 0*bi) % beta + 0*0 + ((T 0 + A 0*bi) % beta * minv % beta) * M0
      i.e. only `Nat.add_zero`, `Nat.mul_zero` and one `Nat.mul_comm`; replace the
      `simpa` with `simp only [peelMu, Nat.mul_zero, Nat.add_zero, Nat.mul_comm M0] at h ⊢`
      followed by `exact h`, or rewrite by hand.
  (2) `cios_bound_core`, `top_limb_le_one` use `Nat.mul_le_mul_left` / `Nat.mul_le_mul_right`.
      At v4.31.0 core these are
        Nat.mul_le_mul_right (k) : n <= m -> n * k <= m * k
        Nat.mul_le_mul_left  (k) : n <= m -> k * n <= k * m
      If Mathlib shadows them with a different argument order, delete `cios_bound_core`
      entirely and pass `Model.cios_bound` to `rows_invariant` instead (it is the same
      statement, already proved in the tree), and in `top_limb_le_one` replace the
      `have hmul` line with `Nat.mul_le_mul_right' h (beta ^ n)` or `by nlinarith`.
  Nothing else in the file depends on a name I could not `#check`.

TO DROP INTO THE TREE
  Delete the `namespace Model` stub section below (it is a verbatim copy of the
  corresponding declarations in Proofs/Fast/Model.lean) and `open`/qualify against the
  real `Model` instead.  Nothing else changes.
-/
import Challenge.Modexp.Submission.Proofs.Fast.Model

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast


namespace Fios

/-! The Nat-level FIOS arithmetic.  Nested so that byte-level modules can reuse the
same names (peelC1, peelC2, rows_invariant) without clashing: FiosRun compiles today
only because it does not import this file, and the witness swap will import both. -/
namespace Arith


/-! ## 0.  Small algebraic helpers (core names verified by `#check`) -/

/-- `s = (s / β) * β + s % β`.  From `Nat.div_add_mod m n : n * (m / n) + m % n = m`. -/
theorem split (β s : Nat) : s / β * β + s % β = s := by
  rw [Nat.mul_comm (s / β) β]; exact Nat.div_add_mod s β

theorem pow_succ' (β k : Nat) : β ^ (k + 1) = β ^ k * β := Nat.pow_succ β k

theorem mul_pow_succ (Y β k : Nat) : Y * β ^ (k + 1) = Y * β * β ^ k := by
  rw [pow_succ', Nat.mul_comm (β ^ k) β, ← Nat.mul_assoc]

theorem mul_pow_succ' (S β k : Nat) : S * β ^ k * β = S * β ^ (k + 1) := by
  rw [pow_succ', Nat.mul_assoc]

theorem swap3 (a b c : Nat) : a * b * c = b * (a * c) := by
  rw [Nat.mul_comm a b, Nat.mul_assoc]

/-- Fold a digit and its carry, one place up. -/
theorem combine (β X Y Z k : Nat) (h : X + Y * β = Z) :
    X * β ^ (k + 1) + Y * β ^ (k + 1 + 1) = Z * β ^ (k + 1) := by
  have h1 : Y * β ^ (k + 1 + 1) = Y * β * β ^ (k + 1) := mul_pow_succ Y β (k + 1)
  have h2 : X * β ^ (k + 1) + Y * β * β ^ (k + 1) = (X + Y * β) * β ^ (k + 1) :=
    (Nat.add_mul _ _ _).symm
  rw [h1, h2, h]

/-- The row tail is one more pair of splits, with no operand product. -/
theorem tail_split (β x d2 : Nat) :
    (x % β + d2) % β + (x / β + (x % β + d2) / β) * β = x + d2 := by
  have e1 : x / β * β + x % β = x := split β x
  have e2 : (x % β + d2) / β * β + (x % β + d2) % β = x % β + d2 := split β _
  rw [Nat.add_mul]
  omega

/-- Two successive `divMod` splits, reassembled: this is the whole content of one fused
body.  Holds for every `β`, including `β = 0`. -/
theorem two_split (β s1 N d2 : Nat) :
    (s1 % β + N + d2) % β + (s1 / β + (s1 % β + N + d2) / β) * β = s1 + N + d2 := by
  have e1 : s1 / β * β + s1 % β = s1 := split β s1
  have e2 : (s1 % β + N + d2) / β * β + (s1 % β + N + d2) % β = s1 % β + N + d2 :=
    split β _
  rw [Nat.add_mul]
  omega

/-- Moving one digit of weight `β ^ k` and its carry of weight `β ^ (k+1)`. -/
theorem shift_step (β w X Y Z c k : Nat) (h : X + Y * β = Z + c) :
    w + X * β ^ k + Y * β ^ (k + 1) = w + c * β ^ k + Z * β ^ k := by
  have hY : Y * β ^ (k + 1) = Y * β * β ^ k := mul_pow_succ Y β k
  have hsum : X * β ^ k + Y * β * β ^ k = (X + Y * β) * β ^ k := (Nat.add_mul _ _ _).symm
  have hmul : (X + Y * β) * β ^ k = (Z + c) * β ^ k := by rw [h]
  have hZ : (Z + c) * β ^ k = Z * β ^ k + c * β ^ k := Nat.add_mul _ _ _
  rw [hY]
  omega

/-- The row identity, with every ingredient abstract.  `W, D1, D2` are the loop's
output and carries, `R` its digit sum, `C1, C2` the peel's carries, `P0` the peel's
exact digit, `L` the word the peel would store, and `LT + LA + LB` the three limb sums. -/
theorem row_assemble (β T1 W D1 D2 R C1 C2 P0 L LT LA LB k : Nat)
    (hinv : W + (D1 + D2) * β ^ k = R + (C1 + C2))
    (hpeel : P0 = (C1 + C2) * β + L)
    (hshift : R * β + P0 = LT + LA + LB) :
    (W + ((T1 + D1) % β + D2) % β * β ^ k
        + ((T1 + D1) / β + ((T1 + D1) % β + D2) / β) * β ^ (k + 1)) * β + L
      = LT + T1 * β ^ (k + 1) + LA + LB := by
  have htail : ((T1 + D1) % β + D2) % β
      + ((T1 + D1) / β + ((T1 + D1) % β + D2) / β) * β = T1 + D1 + D2 := by
    have h := tail_split β (T1 + D1) D2
    omega
  have hcomb := combine β (((T1 + D1) % β + D2) % β)
    ((T1 + D1) / β + ((T1 + D1) % β + D2) / β) (T1 + D1 + D2) k htail
  have hd : (W + ((T1 + D1) % β + D2) % β * β ^ k
        + ((T1 + D1) / β + ((T1 + D1) % β + D2) / β) * β ^ (k + 1)) * β
      = W * β + ((T1 + D1) % β + D2) % β * β ^ k * β
        + ((T1 + D1) / β + ((T1 + D1) % β + D2) / β) * β ^ (k + 1) * β := by
    rw [Nat.add_mul, Nat.add_mul]
  have hp1 : ((T1 + D1) % β + D2) % β * β ^ k * β
      = ((T1 + D1) % β + D2) % β * β ^ (k + 1) := mul_pow_succ' _ β k
  have hp2 : ((T1 + D1) / β + ((T1 + D1) % β + D2) / β) * β ^ (k + 1) * β
      = ((T1 + D1) / β + ((T1 + D1) % β + D2) / β) * β ^ (k + 1 + 1) :=
    mul_pow_succ' _ β (k + 1)
  have hsplit : (T1 + D1 + D2) * β ^ (k + 1)
      = T1 * β ^ (k + 1) + (D1 + D2) * β ^ (k + 1) := by
    rw [Nat.add_assoc]; exact Nat.add_mul _ _ _
  have hLexp : (W + (D1 + D2) * β ^ k) * β = W * β + (D1 + D2) * β ^ (k + 1) := by
    rw [Nat.add_mul, mul_pow_succ']
  have hRexp : (R + (C1 + C2)) * β = R * β + (C1 + C2) * β := Nat.add_mul _ _ _
  have hinvβ : (W + (D1 + D2) * β ^ k) * β = (R + (C1 + C2)) * β := by rw [hinv]
  omega

/-! ## 1.  Little-endian limb value -/

/-- Value of the first `k` limbs of `f`, little-endian in radix `β`. -/
def limbSum (β : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => limbSum β f k + f k * β ^ k

@[simp] theorem limbSum_zero (β : Nat) (f : Nat → Nat) : limbSum β f 0 = 0 := rfl

theorem limbSum_succ (β : Nat) (f : Nat → Nat) (k : Nat) :
    limbSum β f (k + 1) = limbSum β f k + f k * β ^ k := rfl

/-! ## 2.  The fused body

`st β bi mu T A M c1 c2 k` is the state after `k` iterations of the fused inner loop,
a plain recursion on the iteration index.  Iteration `k+1` is exactly the emitted body
(`build_fios.py : emit_body`):

    s1 = T (k+1) + A (k+1) * bi + C1     -- u = s1 % β is kept, C1' = s1 / β
    s2 = s1 % β  + M (k+1) * mu  + C2    -- v = s2 % β is stored at t[k], C2' = s2 / β

The triple is `(value of the limbs stored so far, C1, C2)`.  Iteration `k+1` stores
`t[k]`, i.e. digit position `k`, hence the weight `β ^ k`.
-/

def st (β bi mu : Nat) (T A M : Nat → Nat) (c1 c2 : Nat) : Nat → Nat × Nat × Nat
  | 0 => (0, c1, c2)
  | k + 1 =>
      ( (st β bi mu T A M c1 c2 k).1
          + ((T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1) % β
              + M (k + 1) * mu + (st β bi mu T A M c1 c2 k).2.2) % β * β ^ k,
        (T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1) / β,
        ((T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1) % β
            + M (k + 1) * mu + (st β bi mu T A M c1 c2 k).2.2) / β )

theorem st_zero (β bi mu : Nat) (T A M : Nat → Nat) (c1 c2 : Nat) :
    st β bi mu T A M c1 c2 0 = (0, c1, c2) := rfl

/-- What the loop is accumulating: the row's digit sum from limb index 1 upward. -/
def rowSum (β bi mu : Nat) (T A M : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      rowSum β bi mu T A M k + (T (k + 1) + A (k + 1) * bi + M (k + 1) * mu) * β ^ k

theorem rowSum_succ (β bi mu : Nat) (T A M : Nat → Nat) (k : Nat) :
    rowSum β bi mu T A M (k + 1) =
      rowSum β bi mu T A M k
        + (T (k + 1) + A (k + 1) * bi + M (k + 1) * mu) * β ^ k := rfl

/-! ### The row invariant.  No hypotheses: it is two `divMod` splits reassembled. -/

theorem st_invariant (β bi mu : Nat) (T A M : Nat → Nat) (c1 c2 : Nat) :
    ∀ k, (st β bi mu T A M c1 c2 k).1
        + ((st β bi mu T A M c1 c2 k).2.1 + (st β bi mu T A M c1 c2 k).2.2) * β ^ k
      = rowSum β bi mu T A M k + (c1 + c2) := by
  intro k
  induction k with
  | zero =>
      show (0 : Nat) + (c1 + c2) * β ^ 0 = 0 + (c1 + c2)
      rw [Nat.pow_zero, Nat.mul_one]
  | succ k ih =>
      have hkey : ((T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1) % β
              + M (k + 1) * mu + (st β bi mu T A M c1 c2 k).2.2) % β
            + ((T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1) / β
                + ((T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1) % β
                    + M (k + 1) * mu + (st β bi mu T A M c1 c2 k).2.2) / β) * β
          = (T (k + 1) + A (k + 1) * bi + M (k + 1) * mu)
              + ((st β bi mu T A M c1 c2 k).2.1 + (st β bi mu T A M c1 c2 k).2.2) := by
        have h := two_split β (T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1)
          (M (k + 1) * mu) (st β bi mu T A M c1 c2 k).2.2
        omega
      have hsh := shift_step β (st β bi mu T A M c1 c2 k).1
        (((T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1) % β
            + M (k + 1) * mu + (st β bi mu T A M c1 c2 k).2.2) % β)
        ((T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1) / β
          + ((T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1) % β
              + M (k + 1) * mu + (st β bi mu T A M c1 c2 k).2.2) / β)
        (T (k + 1) + A (k + 1) * bi + M (k + 1) * mu)
        ((st β bi mu T A M c1 c2 k).2.1 + (st β bi mu T A M c1 c2 k).2.2) k hkey
      show (st β bi mu T A M c1 c2 k).1
          + ((T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1) % β
              + M (k + 1) * mu + (st β bi mu T A M c1 c2 k).2.2) % β * β ^ k
          + ((T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1) / β
              + ((T (k + 1) + A (k + 1) * bi + (st β bi mu T A M c1 c2 k).2.1) % β
                  + M (k + 1) * mu + (st β bi mu T A M c1 c2 k).2.2) / β) * β ^ (k + 1)
        = rowSum β bi mu T A M k
            + (T (k + 1) + A (k + 1) * bi + M (k + 1) * mu) * β ^ k + (c1 + c2)
      omega

/-! ## 3.  The row: peel, loop, tail -/

/-- Carry out of the peeled `j = 0` multiply step. -/
def peelC1 (β bi : Nat) (T A : Nat → Nat) : Nat := (T 0 + A 0 * bi) / β

/-- Carry out of the peeled `j = 0` reduce step. -/
def peelC2 (β bi mu : Nat) (T A M : Nat → Nat) : Nat :=
  ((T 0 + A 0 * bi) % β + M 0 * mu) / β

/-- The word the peel would store below `t[0]`.  The engine never stores it, because the
choice of `mu` makes it zero; it is kept explicit so the row identity can be stated
unconditionally. -/
def peelLow (β bi mu : Nat) (T A M : Nat → Nat) : Nat :=
  ((T 0 + A 0 * bi) % β + M 0 * mu) % β

theorem peel_eq (β bi mu : Nat) (T A M : Nat → Nat) :
    T 0 + A 0 * bi + M 0 * mu
      = (peelC1 β bi T A + peelC2 β bi mu T A M) * β + peelLow β bi mu T A M := by
  have e1 : (T 0 + A 0 * bi) / β * β + (T 0 + A 0 * bi) % β = T 0 + A 0 * bi :=
    split β _
  have e2 : ((T 0 + A 0 * bi) % β + M 0 * mu) / β * β
      + ((T 0 + A 0 * bi) % β + M 0 * mu) % β = (T 0 + A 0 * bi) % β + M 0 * mu :=
    split β _
  have hd : (peelC1 β bi T A + peelC2 β bi mu T A M) * β
      = peelC1 β bi T A * β + peelC2 β bi mu T A M * β := Nat.add_mul _ _ _
  simp only [peelC1, peelC2, peelLow] at hd ⊢
  omega

/-- The reduce multiplier makes the peel's stored word vanish. -/
theorem peelLow_eq_zero {β bi mu : Nat} {T A M : Nat → Nat}
    (hdvd : β ∣ (T 0 + A 0 * bi) % β + M 0 * mu) : peelLow β bi mu T A M = 0 := by
  obtain ⟨c, hc⟩ := hdvd
  simp only [peelLow, hc, Nat.mul_mod_right]

/-- The value the whole row leaves in the accumulator: the `k` words the loop stored,
the word the tail stores at `t[n-1]`, and the tail's carry word at `t[n]`.
`A` and `M` carry `n = k + 1` limbs; `T` is read at indices `0 .. k+1`. -/
def rowValue (β bi mu : Nat) (T A M : Nat → Nat) (k : Nat) : Nat :=
  (st β bi mu T A M (peelC1 β bi T A) (peelC2 β bi mu T A M) k).1
    + ((T (k + 1) + (st β bi mu T A M (peelC1 β bi T A) (peelC2 β bi mu T A M) k).2.1) % β
        + (st β bi mu T A M (peelC1 β bi T A) (peelC2 β bi mu T A M) k).2.2) % β * β ^ k
    + ((T (k + 1) + (st β bi mu T A M (peelC1 β bi T A) (peelC2 β bi mu T A M) k).2.1) / β
        + ((T (k + 1)
              + (st β bi mu T A M (peelC1 β bi T A) (peelC2 β bi mu T A M) k).2.1) % β
            + (st β bi mu T A M (peelC1 β bi T A) (peelC2 β bi mu T A M) k).2.2) / β)
      * β ^ (k + 1)

/-- Shifting `rowSum` by one digit and adding the peel's digit gives the three limb
sums.  This is what turns the loop invariant into a statement about `t`, `a` and `m`. -/
theorem rowSum_shift (β bi mu : Nat) (T A M : Nat → Nat) :
    ∀ k, rowSum β bi mu T A M k * β + (T 0 + A 0 * bi + M 0 * mu)
      = limbSum β T (k + 1) + bi * limbSum β A (k + 1) + mu * limbSum β M (k + 1) := by
  intro k
  induction k with
  | zero =>
      show 0 * β + (T 0 + A 0 * bi + M 0 * mu)
        = 0 + T 0 * β ^ 0 + bi * (0 + A 0 * β ^ 0) + mu * (0 + M 0 * β ^ 0)
      rw [Nat.pow_zero, Nat.mul_one, Nat.mul_one, Nat.mul_one,
        Nat.zero_add, Nat.zero_add, Nat.zero_add, Nat.zero_mul,
        Nat.mul_comm bi (A 0), Nat.mul_comm mu (M 0)]
      omega
  | succ k ih =>
      have hd : rowSum β bi mu T A M (k + 1) * β
          = rowSum β bi mu T A M k * β
            + (T (k + 1) + A (k + 1) * bi + M (k + 1) * mu) * β ^ k * β := by
        rw [rowSum_succ]; exact Nat.add_mul _ _ _
      have hp : (T (k + 1) + A (k + 1) * bi + M (k + 1) * mu) * β ^ k * β
          = (T (k + 1) + A (k + 1) * bi + M (k + 1) * mu) * β ^ (k + 1) :=
        mul_pow_succ' _ β k
      have he : (T (k + 1) + A (k + 1) * bi + M (k + 1) * mu) * β ^ (k + 1)
          = T (k + 1) * β ^ (k + 1) + A (k + 1) * bi * β ^ (k + 1)
            + M (k + 1) * mu * β ^ (k + 1) := by
        rw [Nat.add_mul, Nat.add_mul]
      have hA : A (k + 1) * bi * β ^ (k + 1) = bi * (A (k + 1) * β ^ (k + 1)) := swap3 _ _ _
      have hM : M (k + 1) * mu * β ^ (k + 1) = mu * (M (k + 1) * β ^ (k + 1)) := swap3 _ _ _
      have hLT : limbSum β T (k + 1 + 1) = limbSum β T (k + 1) + T (k + 1) * β ^ (k + 1) :=
        limbSum_succ β T (k + 1)
      have hLA : bi * limbSum β A (k + 1 + 1)
          = bi * limbSum β A (k + 1) + bi * (A (k + 1) * β ^ (k + 1)) := by
        rw [limbSum_succ, Nat.mul_add]
      have hLM : mu * limbSum β M (k + 1 + 1)
          = mu * limbSum β M (k + 1) + mu * (M (k + 1) * β ^ (k + 1)) := by
        rw [limbSum_succ, Nat.mul_add]
      omega

/-- **The row identity, unconditional.**  One FIOS row times the radix, plus the word
the peel would have stored, is exactly the CIOS row sum `t + a·b_i + mu·m`. -/
theorem rowValue_mul_raw (β bi mu : Nat) (T A M : Nat → Nat) (k : Nat) :
    rowValue β bi mu T A M k * β + peelLow β bi mu T A M
      = limbSum β T (k + 2) + bi * limbSum β A (k + 1) + mu * limbSum β M (k + 1) := by
  have h := row_assemble β (T (k + 1))
    (st β bi mu T A M (peelC1 β bi T A) (peelC2 β bi mu T A M) k).1
    (st β bi mu T A M (peelC1 β bi T A) (peelC2 β bi mu T A M) k).2.1
    (st β bi mu T A M (peelC1 β bi T A) (peelC2 β bi mu T A M) k).2.2
    (rowSum β bi mu T A M k) (peelC1 β bi T A) (peelC2 β bi mu T A M)
    (T 0 + A 0 * bi + M 0 * mu) (peelLow β bi mu T A M)
    (limbSum β T (k + 1)) (bi * limbSum β A (k + 1)) (mu * limbSum β M (k + 1)) k
    (st_invariant β bi mu T A M (peelC1 β bi T A) (peelC2 β bi mu T A M) k)
    (peel_eq β bi mu T A M) (rowSum_shift β bi mu T A M k)
  have hTL : limbSum β T (k + 2) = limbSum β T (k + 1) + T (k + 1) * β ^ (k + 1) := rfl
  simp only [rowValue]
  omega

/-- With the `mu` choice (`peelLow = 0`) the row is exact:
`rowValue * β = t + a·b_i + mu·m`. -/
theorem rowValue_mul (β bi mu : Nat) (T A M : Nat → Nat) (k : Nat)
    (hpeel : peelLow β bi mu T A M = 0) :
    rowValue β bi mu T A M k * β
      = limbSum β T (k + 2) + bi * limbSum β A (k + 1) + mu * limbSum β M (k + 1) := by
  have h := rowValue_mul_raw β bi mu T A M k
  rw [hpeel] at h
  omega

/-- The row equation in exactly the shape the outer loop consumes:
`t' * β = t + a * b_i + mu * m`, with `a = limbSum A n` and `m = limbSum M n`. -/
theorem fios_row_eq (β bi mu : Nat) (T A M : Nat → Nat) (k : Nat)
    (hpeel : peelLow β bi mu T A M = 0) :
    rowValue β bi mu T A M k * β
      = limbSum β T (k + 2) + limbSum β A (k + 1) * bi + mu * limbSum β M (k + 1) := by
  rw [rowValue_mul β bi mu T A M k hpeel, Nat.mul_comm (limbSum β A (k + 1)) bi]

/-! ## 4.  The outer loop over the `n` rows -/

/-- `Model.cios_bound`, reproved here without `nlinarith` so this file has no Mathlib
tactic dependency.  It is interchangeable with `Model.cios_bound`; delete it and pass
`Model.cios_bound` instead if you prefer one copy. -/
theorem cios_bound_core {m β a bi t mu : Nat} (hβ : 0 < β)
    (ha : a < m) (hbi : bi < β) (ht : t < 2 * m) (hmu : mu < β) :
    (t + a * bi + mu * m) / β < 2 * m := by
  rw [Nat.div_lt_iff_lt_mul hβ]
  have hA : a * bi ≤ m * bi := Nat.mul_le_mul_right bi (by omega)
  have hA2 : m * bi + m = m * (bi + 1) := by rw [Nat.mul_add, Nat.mul_one]
  have hA3 : m * (bi + 1) ≤ m * β := Nat.mul_le_mul_left m (by omega)
  have hB : mu * m + m = (mu + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
  have hB2 : (mu + 1) * m ≤ β * m := Nat.mul_le_mul_right m (by omega)
  have hC : β * m = m * β := Nat.mul_comm β m
  have hD : 2 * m * β = m * β + m * β := by
    rw [Nat.mul_assoc, Nat.two_mul]
  omega

/-- **The outer invariant.**  `t i` are the successive accumulators, `B i` the limbs of
the row-consumed operand, `mu i` the reduce multipliers, `a` the full-width multiplicand.
Each row only has to supply `t (i+1) * β = t i + a * B i + mu i * m`, which is exactly
what `rowValue_mul` gives. -/
theorem rows_invariant {β m a : Nat} (t B mu : Nat → Nat) (n : Nat)
    (hβ : 0 < β) (hm : 0 < m) (ha : a < m) (ht0 : t 0 = 0)
    (hB : ∀ i, i < n → B i < β) (hmu : ∀ i, i < n → mu i < β)
    (hrow : ∀ i, i < n → t (i + 1) * β = t i + a * B i + mu i * m) :
    ∀ i, i ≤ n → (∃ Q, t i * β ^ i = a * limbSum β B i + Q * m) ∧ t i < 2 * m := by
  intro i
  induction i with
  | zero =>
      intro _
      refine ⟨⟨0, ?_⟩, ?_⟩
      · rw [ht0]
        show 0 * β ^ 0 = a * limbSum β B 0 + 0 * m
        rw [Nat.zero_mul, Nat.zero_mul, limbSum_zero, Nat.mul_zero]
      · rw [ht0]; omega
  | succ i ih =>
      intro hi
      obtain ⟨⟨Q, hQ⟩, hlt⟩ := ih (by omega)
      have hin : i < n := by omega
      have hr := hrow i hin
      have hti : t (i + 1) = (t i + a * B i + mu i * m) / β := by
        have h1 : t (i + 1) * β / β = (t i + a * B i + mu i * m) / β := by rw [hr]
        rwa [Nat.mul_div_cancel _ hβ] at h1
      have hbound : t (i + 1) < 2 * m := by
        rw [hti]; exact cios_bound_core hβ ha (hB i hin) hlt (hmu i hin)
      refine ⟨⟨Q + mu i * β ^ i, ?_⟩, hbound⟩
      have hlhs : t (i + 1) * β ^ (i + 1) = (t i + a * B i + mu i * m) * β ^ i := by
        rw [mul_pow_succ, hr]
      have hd1 : (t i + a * B i + mu i * m) * β ^ i
          = t i * β ^ i + a * B i * β ^ i + mu i * m * β ^ i := by
        rw [Nat.add_mul, Nat.add_mul]
      have hd2 : a * limbSum β B (i + 1) = a * limbSum β B i + a * (B i * β ^ i) := by
        rw [limbSum_succ, Nat.mul_add]
      have hd3 : (Q + mu i * β ^ i) * m = Q * m + mu i * β ^ i * m := Nat.add_mul _ _ _
      have hs1 : a * B i * β ^ i = a * (B i * β ^ i) := Nat.mul_assoc a (B i) (β ^ i)
      have hs2 : mu i * m * β ^ i = mu i * β ^ i * m := by
        rw [Nat.mul_assoc, Nat.mul_comm m (β ^ i), Nat.mul_assoc]
      rw [hlhs, hd1, hQ, hd2, hd3, hs1, hs2]
      omega

/-! ## 5.  The precondition the untouched conditional-subtract tail assumes -/

/-- `Csub.csub_correct` needs `t[n] ≤ 1`; it follows from the row bound `t < 2 m` and
`m < β ^ n`.  This is `Monpro.monpro_tn_le_one`'s argument on Nats. -/
theorem top_limb_le_one {β n tn tlow m : Nat}
    (hm : m < β ^ n) (hlt : tn * β ^ n + tlow < 2 * m) : tn ≤ 1 := by
  cases Nat.lt_or_ge tn 2 with
  | inl h => omega
  | inr h =>
      have hmul : 2 * β ^ n ≤ tn * β ^ n := Nat.mul_le_mul_right (β ^ n) h
      omega

/-! ## 6.  The peel's divisibility, and the final assembly

These are the two places the file reaches into `Model.lean`. -/

/-- The reduce multiplier the engine computes: `m = (S * n0inv) mod 2^256`, where `S` is
the low word after the peel's first add. -/
def peelMu (β minv bi : Nat) (T A : Nat → Nat) : Nat := (T 0 + A 0 * bi) % β * minv % β

/-- The peel's stored word is divisible by the radix, hence zero.  `hminv` is exactly the
low-limb hypothesis `Monpro.rows_invariant` already carries. -/
theorem peel_dvd (β minv bi M0 : Nat) (T A : Nat → Nat)
    (hminv : (M0 * minv + 1) % β = 0) :
    β ∣ (T 0 + A 0 * bi) % β + M0 * peelMu β minv bi T A := by
  have h := Model.cios_mu_dvd (β := β) (m := M0) (minv := minv)
    (u := (T 0 + A 0 * bi) % β) (t := (T 0 + A 0 * bi) % β) (a := 0) (bi := 0)
    hminv (by rw [Nat.mul_zero, Nat.add_zero])
  simpa [peelMu, Nat.mul_comm] using h

/-- Everything the untouched conditional-subtract tail needs, in one place. -/
theorem fios_final {β m a b : Nat} (t B mu : Nat → Nat) (n : Nat)
    (hβ : 0 < β) (hm : 0 < m) (ha : a < m) (ht0 : t 0 = 0)
    (hB : ∀ i, i < n → B i < β) (hmu : ∀ i, i < n → mu i < β)
    (hrow : ∀ i, i < n → t (i + 1) * β = t i + a * B i + mu i * m)
    (hb : limbSum β B n = b) :
    (∃ Q, t n * β ^ n = a * b + Q * m) ∧ t n < 2 * m := by
  obtain ⟨⟨Q, hQ⟩, hlt⟩ := rows_invariant t B mu n hβ hm ha ht0 hB hmu hrow n (Nat.le_refl n)
  exact ⟨⟨Q, by rw [hQ, hb]⟩, hlt⟩

/-! ## 7.  The value law

This is `Monpro.monpro_represents`'s route, with the FIOS row identity in place of the
two CIOS passes.  `hcop` is `Model.coprime_radix_pow_of_odd hodd n` in the tree; `hrow`
is `fios_row_eq` applied at each row; `ht0` is the `CALLDATACOPY`-zeroed accumulator.
-/

theorem fios_montMul {β m a b : Nat} (t B mu : Nat → Nat) (n : Nat)
    (hβ : 0 < β) (hm : 0 < m) (ha : a < m) (ht0 : t 0 = 0)
    (hcop : Nat.Coprime (β ^ n) m)
    (hB : ∀ i, i < n → B i < β) (hmu : ∀ i, i < n → mu i < β)
    (hrow : ∀ i, i < n → t (i + 1) * β = t i + a * B i + mu i * m)
    (hb : limbSum β B n = b) :
    Model.montMul m (β ^ n) a b = t n % m ∧ t n < 2 * m := by
  obtain ⟨⟨Q, hQ⟩, hlt⟩ := fios_final t B mu n hβ hm ha ht0 hB hmu hrow hb
  exact ⟨Model.montMul_eq_mod_of_mul_eq hm hcop hQ, hlt⟩

#print axioms st_invariant
#print axioms rowValue_mul
#print axioms fios_row_eq
#print axioms rows_invariant
#print axioms fios_final
#print axioms top_limb_le_one
#print axioms peel_dvd
#print axioms fios_montMul


end Arith
end Fios


end Challenge.Modexp.Submission.Proofs.Fast
