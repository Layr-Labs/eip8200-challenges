import Challenge.Modexp.Submission.Proofs.Algorithm

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.PrimeEval

open EvmSemantics EvmSemantics.EVM

/-- Structurally recursive evaluator; its fuel bound is proved before use. -/
def eval : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, acc, _, _ => acc
  | fuel + 1, base, acc, modulus, exponent =>
    if exponent = 0 then acc else
      eval fuel ((base * base) % modulus)
        (if exponent % 2 = 1 then (acc * base) % modulus else acc)
        modulus (exponent / 2)

theorem eval_eq (fuel base acc modulus exponent : Nat) (bound : exponent < 2^fuel) :
    eval fuel base acc modulus exponent = Precompile.modPowAux base acc modulus exponent := by
  induction fuel generalizing base acc exponent with
  | zero =>
    have he : exponent = 0 := by simpa using bound
    subst exponent
    rw [eval, Precompile.modPowAux]
    rfl
  | succ fuel ih =>
    rw [eval, Precompile.modPowAux]
    by_cases he : exponent = 0
    · simp only [he, if_pos, dif_pos]
    · simp only [he]
      apply ih
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
      simpa only [Nat.pow_succ] using bound

theorem modPow_eq_eval (fuel base exponent modulus : Nat) (bound : exponent < 2^fuel)
    (hm : 1 < modulus) :
    Precompile.modPow base exponent modulus = eval fuel (base % modulus) 1 modulus exponent := by
  rw [eval_eq fuel _ _ _ _ bound, Precompile.modPow,
    if_neg (by omega : modulus ≠ 0), if_neg (by omega : modulus ≠ 1)]

example : eval 256 3 1
    21888242871839275222246405745257275088696311157297823662689037894645226208583
    21888242871839275222246405745257275088696311157297823662689037894645226208582 = 1 := by
  decide

end Challenge.Modexp.Submission.Proofs.PrimeEval
