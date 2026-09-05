import Challenge.Modexp.Spec
import Mathlib.Tactic

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Certificate
open EvmSemantics.EVM

def modulus : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583
def base : Nat := 5964364953636342908918930162962566239787286640968493902593843747347131818633
def exponent : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208581
def answer : Nat := 6720979588572738974916628410083100159223021409556719026881700545747062357561

theorem certificate : Precompile.modPow base exponent modulus = answer := by
  norm_num [Precompile.modPow, Precompile.modPowAux, modulus, base, exponent, answer]

end Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Certificate
