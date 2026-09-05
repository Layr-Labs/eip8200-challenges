import Challenge.Modexp.Scorer
import Mathlib.Tactic

namespace Challenge.Modexp.Submission.Proofs.Fast.RSA257Certificate
open EvmSemantics.EVM

def modulus : Nat := 2^256 + 7
def base : Nat := 2^256 + 5
def answer : Nat := 2^256 - 1

private theorem hs0 : base * base % modulus = 4 := by
  decide

private theorem hfinal : base * 4 % modulus = answer := by
  decide

theorem certificate : Precompile.modPow base 3 modulus = answer := by
  have hm0 : modulus ≠ 0 := by decide
  have hm1 : modulus ≠ 1 := by decide
  have hb : base % modulus = base := by decide
  simp [Precompile.modPow, Precompile.modPowAux, hm0, hm1, hb, hs0, hfinal]

end Challenge.Modexp.Submission.Proofs.Fast.RSA257Certificate
