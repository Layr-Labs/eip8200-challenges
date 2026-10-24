import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput
import Challenge.Modexp.Submission.Proofs.Fast.Model

set_option warningAsError true
set_option maxHeartbeats 2000000

namespace CycleSubmission.Global.RootE3Scale
open Challenge.Modexp.Submission.Proofs.Fast.Model

/-- Two existing Montgomery products evaluate a cube with asymmetric input scales. -/
theorem asymmetric_cube {m R a S T X Y : Nat} (hm : 0 < m)
    (hcop : Nat.Coprime R m) (hx : X ≡ a * S [MOD m])
    (hy : Y ≡ a * T [MOD m]) (hscale : S * S * T = R * R) :
    montMul m R (montMul m R X X) Y = a ^ 3 % m := by
  have hfirst := montMul_mul_R_modEq hm hcop X X
  have hsecond := montMul_mul_R_modEq hm hcop (montMul m R X X) Y
  have htotal : montMul m R (montMul m R X X) Y * (R * R) ≡
      a ^ 3 * (R * R) [MOD m] := by
    calc
      montMul m R (montMul m R X X) Y * (R * R)
          ≡ (montMul m R X X * Y) * R [MOD m] := by
            simpa only [Nat.mul_assoc] using hsecond.mul_right R
      _ = (montMul m R X X * R) * Y := by ring
      _ ≡ (X * X) * Y [MOD m] := hfirst.mul_right Y
      _ ≡ (a * S) * (a * S) * (a * T) [MOD m] := (hx.mul hx).mul hy
      _ = a ^ 3 * (R * R) := by rw [← hscale]; ring
  have hresult : montMul m R (montMul m R X X) Y ≡ a ^ 3 [MOD m] :=
    htotal.cancel_right_of_coprime (Nat.Coprime.mul_left hcop hcop).symm
  exact (Nat.mod_eq_of_lt (montMul_lt hm _ _ _)).symm.trans hresult

theorem quarter_scale (B k : Nat) :
    B ^ (3 * k) * B ^ (3 * k) * B ^ (2 * k) = B ^ (4 * k) * B ^ (4 * k) := by
  simp only [← Nat.pow_add]
  congr 1
  omega

theorem asymmetric_cube_quarters {m a B k X Y : Nat} (hm : 0 < m)
    (hcop : Nat.Coprime (B ^ (4 * k)) m)
    (hx : X ≡ a * B ^ (3 * k) [MOD m])
    (hy : Y ≡ a * B ^ (2 * k) [MOD m]) :
    montMul m (B ^ (4 * k)) (montMul m (B ^ (4 * k)) X X) Y = a ^ 3 % m :=
  asymmetric_cube hm hcop hx hy (quarter_scale B k)

end CycleSubmission.Global.RootE3Scale
