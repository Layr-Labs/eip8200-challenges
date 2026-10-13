import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTableBuild
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInit
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneReturn
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowPrecopyRoute

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

/-- The returned state of the precopy route (`WindowPrecopyRoute`). -/
abbrev returnedState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  WindowPrecopyRoute.returnedState template base modulus exponent rest

theorem core_result (template : State) (base modulus exponent : UInt256)
    (hmodulus : 0 < modulus.toNat) (rest : List UInt256) :
    (returnedState template base modulus exponent rest).toResult =
      .returned (Precompile.natToBytes (base.toNat ^ exponent.toNat % modulus.toNat) 32) :=
  WindowPrecopyRoute.core_result template base modulus exponent hmodulus rest

/-- With a zero modulus every `MULMOD` of the last step yields zero, so the
window core returns the precompile's zero word without a separate exit. -/
theorem core_result_zero (template : State) (base modulus exponent : UInt256)
    (hmodulus : modulus.toNat = 0) (rest : List UInt256) :
    (returnedState template base modulus exponent rest).toResult =
      .returned (Precompile.natToBytes 0 32) :=
  WindowPrecopyRoute.core_result_zero template base modulus exponent hmodulus rest

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCore
