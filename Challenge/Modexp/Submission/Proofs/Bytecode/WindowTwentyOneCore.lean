import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTableBuild
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInit
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneReturn

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def returnedState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  let finish := WindowTwentyOneLoop.finishState template base modulus exponent rest
  WindowTwentyOneReturn.returned finish (UInt256.ofNat 2963)
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63) 19 finish.stack.tail

theorem run_finish (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions WindowTwentyOneReturn.program
      (WindowTwentyOneLoop.finishState template base modulus exponent rest) =
    some (returnedState template base modulus exponent rest) := by
  let finish := WindowTwentyOneLoop.finishState template base modulus exponent rest
  have htail : finish.stack.tail.length + 3 < 1024 := by
    simp only [finish, WindowTwentyOneLoop.finishState, WindowTwentyOneGroup.state,
      WindowTwentyOneLookup.framed, List.replicate_zero, List.nil_append, List.cons_append,
      List.tail_cons, List.length_cons]
    omega
  have h := WindowTwentyOneReturn.run_return finish (UInt256.ofNat 2958)
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63) 19 (by decide) rfl
    finish.stack.tail htail
  have hpc : advancePC 5 (UInt256.ofNat 2958) = UInt256.ofNat 2963 := by decide
  simpa only [returnedState, finish, WindowTwentyOneReturn.framed, WindowTwentyOneLoop.finishState,
    WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, List.replicate_zero,
    List.nil_append, List.cons_append, List.tail_cons, hpc] using h

theorem core_result (template : State) (base modulus exponent : UInt256)
    (hmodulus : 0 < modulus.toNat) (rest : List UInt256) :
    (returnedState template base modulus exponent rest).toResult =
      .returned (Precompile.natToBytes (base.toNat ^ exponent.toNat % modulus.toNat) 32) := by
  unfold returnedState
  rw [WindowTwentyOneReturn.returned_result]
  have he : exponent.toNat < 16 ^ 64 := by
    change exponent.toNat < 2 ^ 256
    exact exponent.val.isLt
  have h := WindowTwentyOneMath.three_bodies_toNat base modulus exponent.toNat hmodulus he
  rw [h]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCore
