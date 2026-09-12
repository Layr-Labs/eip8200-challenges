import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTableBuild
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInit
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneReturn

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def program : List Instr :=
  WindowTwentyOneTableBuild.program ++ WindowTwentyOneInit.program ++
    WindowTwentyOneLoop.repeatProgram 3 ++ WindowTwentyOneReturn.program

def returnedState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  let finish := WindowTwentyOneLoop.finishState template base modulus exponent rest
  WindowTwentyOneReturn.returned finish (UInt256.ofNat 2869)
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63) 16 finish.stack.tail

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
  have h := WindowTwentyOneReturn.run_return finish (UInt256.ofNat 2864)
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63) 16 (by decide) rfl
    finish.stack.tail htail
  have hpc : advancePC 5 (UInt256.ofNat 2864) = UInt256.ofNat 2869 := by decide
  simpa only [returnedState, finish, WindowTwentyOneReturn.framed, WindowTwentyOneLoop.finishState,
    WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, List.replicate_zero,
    List.nil_append, List.cons_append, List.tail_cons, hpc] using h

/-- Complete arithmetic path, from the normalized base through the returned word.
Calldata pointer witnesses and the loop jump certificate remain explicit. -/
theorem run_core (template : State) (base modulus exponentOffset modulusOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (he : rest[4]? = some exponentOffset) (hm : rest[5]? = some modulusOffset)
    (hmodulus : MachineState.readWord template.executionEnv.calldata modulusOffset.toNat = modulus)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 2401 = true) :
    runInstructions program
      (WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 2264) base modulus rest) =
    some (returnedState template base modulus
      (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat) rest) := by
  let exponent := MachineState.readWord template.executionEnv.calldata exponentOffset.toNat
  have ht := WindowTwentyOneTableBuild.run_all template base modulus exponentOffset rest hrest he
  have hi := WindowTwentyOneInit.run_enter template base modulus exponent modulusOffset rest hrest hm hmodulus
  have hl := WindowTwentyOneLoop.run_three template base modulus exponent rest hrest hjump
  have hr := run_finish template base modulus exponent rest hrest
  have hi' : runInstructions WindowTwentyOneInit.program
      (WindowTwentyOneTable.framed template (UInt256.ofNat 2380) base modulus 16 ([base, exponent] ++ rest)) =
      some (WindowTwentyOneLoop.loopState template base modulus exponent 0 rest) := by
    simpa only [WindowTwentyOneLoop.loopState, WindowTwentyOneMath.accumulator, WindowTwentyOneMath.advance] using hi
  have hti := runInstructions_append_some _ _ _ _ _ ht hi'
  have htil := runInstructions_append_some _ _ _ _ _ hti hl
  exact runInstructions_append_some _ _ _ _ _ htil hr

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
