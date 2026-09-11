import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option warningAsError true

/-!
Arithmetic research lemmas for triangular Montgomery squaring.
These do not assert execution of the candidate EVM bytecode. The instruction
traces, memory agreement, and top-level challenge theorem remain separate work.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareArithmetic

def value (b : Nat) : List Nat → Nat
  | [] => 0
  | a :: xs => a + b * value b xs

def triangular (b : Nat) : List Nat → Nat
  | [] => 0
  | a :: xs => a*a + 2*a*b*value b xs + b*b*triangular b xs

/-- Each off-diagonal product occurs once with coefficient two. -/
theorem triangular_eq_square (b : Nat) (xs : List Nat) :
    triangular b xs = value b xs * value b xs := by
  induction xs with
  | nil => simp [triangular, value]
  | cons a xs ih => simp only [triangular, value, ih]; ring

/-- The carry bit from the previous digit must be cleared on the first
    off-diagonal digit. Higher digits retain their ordinary doubling carries. -/
theorem clear_link_bit (x h : Nat) (hh : h < 2) :
    ((2*x+h)/2)*2 = 2*x := by
  omega

/-- A doubling pass emits a single carry bit for every bounded digit. -/
theorem doubling_carry_lt_two {b a h : Nat} (hb : 0 < b)
    (ha : a < b) (hh : h < 2) : (2*a+h)/b < 2 := by
  rw [Nat.div_lt_iff_lt_mul hb]
  omega

/-- Montgomery cancellation works with any exact row, including a triangular
    row. No CIOS-specific intermediate `t < 2*m` assumption is imposed. -/
theorem row_invariant {b t row q m p total accumulatedQ : Nat}
    (hinv : t*p = total + accumulatedQ*m)
    (hdiv : b ∣ t+row+q*m) :
    ((t+row+q*m)/b)*(b*p) =
      (total+row*p)+(accumulatedQ+q*p)*m := by
  have hexact := Nat.div_mul_cancel hdiv
  calc
    ((t+row+q*m)/b)*(b*p) = ((t+row+q*m)/b*b)*p := by ring
    _ = (t+row+q*m)*p := by rw [hexact]
    _ = t*p + row*p + q*p*m := by ring
    _ = (total+row*p)+(accumulatedQ+q*p)*m := by rw [hinv]; ring

/-- After consuming the low block l of a=l+p*h, the triangular numerator
    contains exactly a^2 minus the as-yet-unprocessed high square. -/
theorem consumed_product (l p h : Nat) :
    (l*l+2*l*p*h)+(p*h)*(p*h) = (l+p*h)*(l+p*h) := by
  ring

/-- Triangular partial accumulators use the weaker bound 2*a+m. In
    particular they fit below 3*R when both operands and modulus fit R. -/
theorem partial_bound {p l a total q m : Nat} (hp : 0 < p)
    (hm : 0 < m) (hl : l ≤ p) (hq : q < p)
    (htotal : total + l*l = 2*a*l) :
    (total+q*m)/p < 2*a+m := by
  rw [Nat.div_lt_iff_lt_mul hp]
  have hprod : 2*a*l ≤ 2*a*p := Nat.mul_le_mul_left (2*a) hl
  have hqprod : q*m < p*m := Nat.mul_lt_mul_of_pos_right hq hm
  nlinarith

/-- The final exact quotient needs at most one conditional subtraction. -/
theorem final_bound {R a m q : Nat} (hR : 0 < R)
    (ha : a < m) (hmR : m < R) (hq : q < R) :
    (a*a+q*m)/R < 2*m := by
  rw [Nat.div_lt_iff_lt_mul hR]
  have hm : 0 < m := by omega
  have haa : a*a ≤ a*m := Nat.mul_le_mul_left a (Nat.le_of_lt ha)
  have ham : a*m < R*m := Nat.mul_lt_mul_of_pos_right (lt_trans ha hmR) hm
  have hqm : q*m < R*m := Nat.mul_lt_mul_of_pos_right hq hm
  nlinarith

/-- The contribution added by row `i`, before the Montgomery division. -/
def rowTerm (b a i : Nat) : Nat :=
  (a / b^i % b)^2 * b^i + 2*(a / b^i % b)*(a / b^(i+1))*b^(i+1)

/-- Contributions are weighted by the preceding Montgomery divisions. -/
def consumed (b a : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => consumed b a i + rowTerm b a i * b^i

theorem high_split (b a i : Nat) :
    a / b^i = a / b^i % b + b * (a / b^(i+1)) := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  exact (Nat.mod_add_div (a / b^i) b).symm

theorem rowTerm_square (b a i : Nat) :
    rowTerm b a i * b^i + (a / b^(i+1) * b^(i+1))^2 =
      (a / b^i * b^i)^2 := by
  have h := high_split b a i
  calc
    _ = ((a / b^i % b + b * (a / b^(i+1))) * b^i)^2 := by
      simp only [rowTerm, pow_succ]
      ring
    _ = _ := by rw [← h]

/-- A partial triangular product plus the unconsumed high square is `a²`. -/
theorem consumed_square (b a i : Nat) :
    consumed b a i + (a / b^i * b^i)^2 = a^2 := by
  induction i with
  | zero => simp [consumed]
  | succ i ih =>
    rw [consumed, Nat.add_assoc, rowTerm_square, ih]

theorem consumed_final (b a n : Nat) (ha : a < b^n) :
    consumed b a n = a*a := by
  have h := consumed_square b a n
  simpa [Nat.div_eq_of_lt ha, pow_two] using h

/-- The partial product is bounded by twice `a` times the consumed low block. -/
theorem consumed_low (b a i : Nat) :
    consumed b a i + (a % b^i)^2 = 2*a*(a % b^i) := by
  have h := consumed_square b a i
  have hd := Nat.mod_add_div a (b^i)
  have hsq := congrArg (fun x : Nat => x^2) hd
  have hmul := congrArg (fun x : Nat => x*(a % b^i)) hd
  nlinarith

/-- Exact EVM row equations imply the triangular Montgomery invariant. -/
theorem accumulate (b a m n : Nat) (t q : Nat → Nat)
    (ht0 : t 0 = 0)
    (hstep : ∀ i, i < n → t (i+1)*b = t i + rowTerm b a i + q i*m) :
    ∀ i, i ≤ n → t i*b^i = consumed b a i +
      (List.sum ((List.range i).map (fun j => q j*b^j)))*m := by
  intro i
  induction i with
  | zero => simp [ht0, consumed]
  | succ i ih =>
    intro hi
    have prev := ih (by omega)
    have step := hstep i (by omega)
    rw [consumed, List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    calc
      _ = (t (i+1)*b)*b^i := by rw [pow_succ]; ring
      _ = (t i + rowTerm b a i + q i*m)*b^i := by rw [step]
      _ = t i*b^i + rowTerm b a i*b^i + q i*b^i*m := by ring
      _ = _ := by rw [prev]; ring

theorem quotient_digits_bound (b n : Nat) (hb : 0 < b) (q : Nat → Nat)
    (hq : ∀ i, i < n → q i < b) :
    List.sum ((List.range n).map (fun i => q i*b^i)) < b^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have prev := ih (fun i hi => hq i (by omega))
    have cur := hq n (by omega)
    have hp : 0 < b^n := pow_pos hb n
    rw [List.range_succ, List.map_append, List.sum_append, pow_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    nlinarith

/-- Final squaring accumulators are exactly `(a²+Q*m)/R`, with `Q<R`.
The concrete EVM proof supplies the exact row equations and bounded `q` words. -/
theorem final_quotient (b a m n : Nat) (hb : 0 < b) (ha : a < b^n)
    (t q : Nat → Nat) (ht0 : t 0 = 0)
    (hstep : ∀ i, i < n → t (i+1)*b = t i + rowTerm b a i + q i*m)
    (hq : ∀ i, i < n → q i < b) :
    ∃ Q, Q < b^n ∧ t n*b^n = a*a+Q*m := by
  refine ⟨_, quotient_digits_bound b n hb q hq, ?_⟩
  have h := accumulate b a m n t q ht0 hstep n (by omega)
  rwa [consumed_final b a n ha] at h

end Challenge.Modexp.Submission.Proofs.Fast.SquareArithmetic
