import Challenge.Modexp.Submission.Proofs.Cycle.Core
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 4096
namespace CycleSubmission.CallerArithmetic
open Challenge.Modexp.Submission.Proofs.Fast

abbrev R : Nat := 2^2048
def decode (N A : Nat) : Nat := Model.montMul N R A 1

theorem coprime (N : Nat) (hodd : Odd N) : Nat.Coprime R N := by
  exact Model.coprime_radix_pow_of_odd (Nat.odd_iff.mp hodd) 8

theorem decode_form (N A : Nat) (hN : 0 < N) (hodd : Odd N) :
    A ≡ decode N A * R [MOD N] := by
  have h := Model.montMul_mul_R_modEq hN (coprime N hodd) A 1
  simpa only [mul_one, decode] using h.symm

theorem iterate_form (N A x k : Nat) (hN : 0 < N) (hodd : Odd N)
    (hform : A ≡ x * R [MOD N]) :
    ((fun a => Model.montMul N R a a)^[k] A) ≡ x^(2^k) * R [MOD N] := by
  induction k with
  | zero => simpa only [Function.iterate_zero_apply, pow_zero, pow_one] using hform
  | succ k ih =>
    rw [Function.iterate_succ_apply', Model.montMul_form hN (coprime N hodd) ih ih]
    have he : x^(2^k) * x^(2^k) = x^(2^(k+1)) := by
      rw [← pow_add, pow_succ, Nat.mul_two]
    rw [he]
    exact Nat.mod_modEq _ N

/-- The terminal routine computes exactly the old abstract square-chain product,
including when its two operands use the asymmetric exponent-three scaling. -/
theorem product_eq (N A B k : Nat) (hN : 0 < N) (hodd : Odd N) :
    Model.montMul N R ((fun a => Model.montMul N R a a)^[k] A) B =
      B * (decode N A)^(2^k) % N := by
  rw [Model.montMul_comm]
  exact Model.montMul_const_form hN (coprime N hodd)
    (iterate_form N A (decode N A) k hN hodd (decode_form N A hN hodd)) B

theorem ordinary_power (N A B x k : Nat) (hN : 0 < N) (hodd : Odd N)
    (ha : A ≡ x*R [MOD N]) (hb : B ≡ x [MOD N]) :
    Model.montMul N R ((fun a => Model.montMul N R a a)^[k] A) B =
      x^(2^k+1) % N := by
  rw [product_eq N A B k hN hodd]
  have hd : decode N A ≡ x [MOD N] :=
    ((decode_form N A hN hodd).symm.trans ha).cancel_right_of_coprime (coprime N hodd).symm
  have h := hb.mul (hd.pow (2^k))
  simpa only [Nat.ModEq, pow_succ, Nat.mul_comm] using h

/-- Inherited asymmetric-cube identity, specialized to the old eight-word
Montgomery factor. The algebra follows RootE3Scale.asymmetric_cube in v14. -/
theorem asymmetric_cube (N A B x S T : Nat) (hN : 0 < N) (hodd : Odd N)
    (ha : A ≡ x*S [MOD N]) (hb : B ≡ x*T [MOD N])
    (hscale : S*S*T = R*R) :
    Model.montMul N R (Model.montMul N R A A) B = x^3 % N := by
  have hcop := coprime N hodd
  have hfirst := Model.montMul_mul_R_modEq hN hcop A A
  have hsecond := Model.montMul_mul_R_modEq hN hcop (Model.montMul N R A A) B
  have htotal : Model.montMul N R (Model.montMul N R A A) B * (R*R) ≡
      x^3 * (R*R) [MOD N] := by
    calc
      Model.montMul N R (Model.montMul N R A A) B * (R*R)
          ≡ (Model.montMul N R A A * B) * R [MOD N] := by
            simpa only [Nat.mul_assoc] using hsecond.mul_right R
      _ = (Model.montMul N R A A * R) * B := by ring
      _ ≡ (A*A)*B [MOD N] := hfirst.mul_right B
      _ ≡ (x*S)*(x*S)*(x*T) [MOD N] := (ha.mul ha).mul hb
      _ = x^3*(R*R) := by rw [← hscale]; ring
  have hresult := htotal.cancel_right_of_coprime (Nat.Coprime.mul_left hcop hcop).symm
  exact (Nat.mod_eq_of_lt (Model.montMul_lt hN _ _ _)).symm.trans hresult

end CycleSubmission.CallerArithmetic
