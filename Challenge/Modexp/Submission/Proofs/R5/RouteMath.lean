import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Cycle.SelectedRadix
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-!
# The arithmetic of the r5 route

`R = 2^1200` is the r5 Montgomery radix, `R4 = 2^1024` the leader's. With `u = A * R4⁻¹` in
`ZMod N`, the start value `A * 2^176 = u * R`, every square maps `u^(2^i) * R` to
`u^(2^(i+1)) * R`, the product with `B` gives `u^(2^k) * B`, and so does the leader's
`result N A B k` (its iterated `montMul` at `R4`). Bounds: `X + 2N ≤ R` is preserved by a
square (`4N ≤ R`), and the product is below `2N`.
-/

namespace CycleSubmission.R5.RouteMath
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

def R : Nat := 2^1200
def R4 : Nat := Limbs.radix^4

theorem R_eq : R = R4 * 2^176 := by norm_num [R, R4, Limbs.radix]

theorem coprime_two_pow (e N : Nat) (hodd : N % 2 = 1) : Nat.Coprime (2^e) N := by
  apply Nat.Coprime.pow_left
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)

theorem coprime_R (N : Nat) (hodd : N % 2 = 1) : Nat.Coprime R N := coprime_two_pow 1200 N hodd

theorem coprime_R4 (N : Nat) (hodd : N % 2 = 1) : Nat.Coprime R4 N := by
  have h : R4 = 2^1024 := by norm_num [R4, Limbs.radix]
  rw [h]; exact coprime_two_pow 1024 N hodd

/-- A square keeps `X ≤ R - 2N`. -/
theorem square_bound (N R T X Z Q : Nat) (hT : T + 2*N = R) (h4 : 4*N ≤ R) (hR : 0 < R)
    (hX : X ≤ T) (hQ : Q < R) (hex : Z*R = X*X + Q*N) : Z ≤ T := by
  by_contra h
  have h' : T + 1 ≤ Z := by omega
  have hZ : (T+1)*R ≤ Z*R := Nat.mul_le_mul_right R h'
  have hXX : X*X ≤ T*T := Nat.mul_le_mul hX hX
  have hQN : (Q+1)*N ≤ R*N := Nat.mul_le_mul_right N hQ
  have hTN : 2*N ≤ T := by omega
  have hNT : 2*N*N ≤ T*N := Nat.mul_le_mul_right N hTN
  nlinarith

/-- The final product is below `2N`. -/
theorem product_bound (N R X B T Q : Nat) (hR : 0 < R) (hN : 0 < N) (hX : X < R) (hB : B < N)
    (hQ : Q < R) (hex : T*R = X*B + Q*N) : T < 2*N :=
  CycleSubmission.Radix.finalProductRange R N X B Q T hR hN hX hB hQ hex

theorem cancel_R {N : Nat} (R' : Nat) (hcop : Nat.Coprime R' N) (a b : ZMod N)
    (h : a * R' = b * R') : a = b := by
  have h1 : (R' : ZMod N) * (R' : ZMod N)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one R' hcop
  calc a = a * R' * (R' : ZMod N)⁻¹ := by rw [mul_assoc, h1, mul_one]
    _ = b * R' * (R' : ZMod N)⁻¹ := by rw [h]
    _ = b := by rw [mul_assoc, h1, mul_one]

/-- One square in `ZMod N`. -/
theorem square_zmod {N : Nat} (hodd : N % 2 = 1) (u : ZMod N) (X Z Q : Nat)
    (hX : (X : ZMod N) = u * R) (hex : Z*R = X*X + Q*N) : (Z : ZMod N) = u^2 * R := by
  apply cancel_R R (coprime_R N hodd)
  have h := congrArg (fun n : Nat => (n : ZMod N)) hex
  push_cast at h
  rw [ZMod.natCast_self, mul_zero, add_zero, hX] at h
  rw [h]; ring

/-- The product in `ZMod N`. -/
theorem product_zmod {N : Nat} (hodd : N % 2 = 1) (u : ZMod N) (X B T Q : Nat)
    (hX : (X : ZMod N) = u * R) (hex : T*R = X*B + Q*N) : (T : ZMod N) = u * B := by
  apply cancel_R R (coprime_R N hodd)
  have h := congrArg (fun n : Nat => (n : ZMod N)) hex
  push_cast at h
  rw [ZMod.natCast_self, mul_zero, add_zero, hX] at h
  rw [h]; ring

theorem regroup {N : Nat} (a r x : ZMod N) (h : r * r⁻¹ = 1) : a * x = a * r⁻¹ * (r * x) := by
  calc a * x = a * x * (r * r⁻¹) := by rw [h, mul_one]
    _ = _ := by ring

/-- The start value `A * 2^176` is `u * R` with `u = A * R4⁻¹`. -/
theorem start_zmod {N : Nat} (hodd : N % 2 = 1) (A : Nat) :
    ((A * 2^176 : Nat) : ZMod N) = ((A : ZMod N) * (R4 : ZMod N)⁻¹) * R := by
  have h1 : (R4 : ZMod N) * (R4 : ZMod N)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one R4 (coprime_R4 N hodd)
  rw [R_eq, Nat.cast_mul, Nat.cast_mul]
  exact regroup _ _ _ h1

/-- The leader's terminal value. -/
def result (N A B k : Nat) : Nat :=
  Model.montMul N R4 ((fun a => Model.montMul N R4 a a)^[k] A) B

theorem montMul_cast {N : Nat} (hN : 0 < N) (R' x y : Nat) :
    (Model.montMul N R' x y : ZMod N) = (x : ZMod N) * y * (R' : ZMod N)⁻¹ := by
  haveI : NeZero N := ⟨hN.ne'⟩
  unfold Model.montMul
  rw [ZMod.natCast_zmod_val]

theorem iterate_zmod {N : Nat} (hN : 0 < N) (hodd : N % 2 = 1) (A : Nat) (k : Nat) :
    (((fun a => Model.montMul N R4 a a)^[k] A : Nat) : ZMod N) =
      ((A : ZMod N) * (R4 : ZMod N)⁻¹)^(2^k) * R4 := by
  have h1 : (R4 : ZMod N) * (R4 : ZMod N)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one R4 (coprime_R4 N hodd)
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id, pow_zero, pow_one]
    calc (A : ZMod N) = A * ((R4 : ZMod N) * (R4 : ZMod N)⁻¹) := by rw [h1, mul_one]
      _ = _ := by ring
  | succ k ih =>
    rw [Function.iterate_succ_apply', montMul_cast hN, ih, pow_succ, pow_mul]
    calc (((A : ZMod N) * (R4 : ZMod N)⁻¹)^(2^k) * R4) * (((A : ZMod N) * (R4 : ZMod N)⁻¹)^(2^k) * R4)
          * (R4 : ZMod N)⁻¹
        = (((A : ZMod N) * (R4 : ZMod N)⁻¹)^(2^k))^2 * R4 * ((R4 : ZMod N) * (R4 : ZMod N)⁻¹) := by ring
      _ = _ := by rw [h1, mul_one]

theorem result_zmod {N : Nat} (hN : 0 < N) (hodd : N % 2 = 1) (A B k : Nat) :
    result N A B k = (((A : ZMod N) * (R4 : ZMod N)⁻¹)^(2^k) * B).val := by
  have h1 : (R4 : ZMod N) * (R4 : ZMod N)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one R4 (coprime_R4 N hodd)
  unfold result
  rw [show Model.montMul N R4 ((fun a => Model.montMul N R4 a a)^[k] A) B =
      ((((fun a => Model.montMul N R4 a a)^[k] A : Nat) : ZMod N) * (B : ZMod N) * (R4 : ZMod N)⁻¹).val
      from rfl, iterate_zmod hN hodd A k]
  congr 1
  calc ((A : ZMod N) * (R4 : ZMod N)⁻¹)^(2^k) * R4 * B * (R4 : ZMod N)⁻¹
      = ((A : ZMod N) * (R4 : ZMod N)⁻¹)^(2^k) * B * ((R4 : ZMod N) * (R4 : ZMod N)⁻¹) := by ring
    _ = _ := by rw [h1, mul_one]

/-- A value below `N` that is congruent to `w` is `w.val`. -/
theorem eq_val_of_cast {N : Nat} (T : Nat) (w : ZMod N) (hT : T < N)
    (h : (T : ZMod N) = w) : T = w.val := by
  rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt hT]

end CycleSubmission.R5.RouteMath
