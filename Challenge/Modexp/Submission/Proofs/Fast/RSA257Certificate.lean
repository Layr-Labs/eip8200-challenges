import Challenge.Modexp.Scorer
import Mathlib.Tactic

namespace Challenge.Modexp.Submission.Proofs.Fast.RSA257Certificate

open EvmSemantics.EVM

def radix : Nat := 2 ^ 256
def base : Nat := radix + 5
def modulus : Nat := radix + 7
def answer : Nat := radix - 1

private theorem hsq : base * base % modulus = 4 := by
  norm_num [base, modulus, radix]

private theorem hfinal : base * 4 % modulus = answer := by
  norm_num [base, modulus, answer, radix]

theorem certificate : Precompile.modPow base 3 modulus = answer := by
  have hm0 : modulus ≠ 0 := by norm_num [modulus, radix]
  have hm1 : modulus ≠ 1 := by norm_num [modulus, radix]
  have hb : base % modulus = base := by norm_num [base, modulus, radix]
  simp [Precompile.modPow, Precompile.modPowAux, hm0, hm1, hb, hsq, hfinal]

end Challenge.Modexp.Submission.Proofs.Fast.RSA257Certificate
