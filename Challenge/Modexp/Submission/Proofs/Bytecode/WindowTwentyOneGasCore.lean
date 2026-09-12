import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof WindowNibbleKernel WindowTwentyOneBinding

structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  table : Block artifact fork 2219 WindowTwentyOneTableBuild.program
  init : Block artifact fork 2335 WindowTwentyOneInit.program
  iteration : Block artifact fork 2356 WindowTwentyOneLoop.iterationProgram
  finish : Block artifact fork 2819 WindowTwentyOneReturn.program

def steps_continue {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256) (count : Nat) (hcount : count < 2)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 2356 = true) :
    GasSteps (WindowTwentyOneLoop.loopState template base modulus exponent count rest)
      (WindowTwentyOneLoop.loopState template base modulus exponent (count + 1) rest) :=
  paths.iteration.steps (env.transfer rfl rfl) rfl
    (WindowTwentyOneLoop.run_continue template base modulus exponent count hcount rest hrest hjump)

def steps_prefix {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256) (count : Nat) (hcount : count ≤ 2)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 2356 = true) :
    GasSteps (WindowTwentyOneLoop.loopState template base modulus exponent 0 rest)
      (WindowTwentyOneLoop.loopState template base modulus exponent count rest) := by
  induction count with
  | zero => exact GasSteps.refl _
  | succ count ih =>
      exact (ih (by omega)).trans
        (steps_continue paths template env base modulus exponent count (by omega) rest hrest hjump)

def steps_three {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256) (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 2356 = true) :
    GasSteps (WindowTwentyOneLoop.loopState template base modulus exponent 0 rest)
      (WindowTwentyOneLoop.finishState template base modulus exponent rest) :=
  (steps_prefix paths template env base modulus exponent 2 (by decide) rest hrest hjump).trans
    (paths.iteration.steps (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_last template base modulus exponent rest hrest hjump))

def steps_core {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponentOffset modulusOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (he : rest[4]? = some exponentOffset) (hm : rest[5]? = some modulusOffset)
    (hmodulus : MachineState.readWord template.executionEnv.calldata modulusOffset.toNat = modulus)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 2356 = true) :
    GasSteps (WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 2219) base modulus rest)
      (WindowTwentyOneCore.returnedState template base modulus
        (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat) rest) := by
  let exponent := MachineState.readWord template.executionEnv.calldata exponentOffset.toNat
  have ht := paths.table.steps
    (s := WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 2219) base modulus rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneTableBuild.run_all template base modulus exponentOffset rest hrest he)
  have hi := WindowTwentyOneInit.run_enter template base modulus exponent modulusOffset rest hrest hm hmodulus
  have hi' : runInstructions WindowTwentyOneInit.program
      (WindowTwentyOneTable.framed template (UInt256.ofNat 2335) base modulus 16 ([base, exponent] ++ rest)) =
      some (WindowTwentyOneLoop.loopState template base modulus exponent 0 rest) := by
    simpa only [WindowTwentyOneLoop.loopState, WindowTwentyOneMath.accumulator, WindowTwentyOneMath.advance] using hi
  have hinit := paths.init.steps
    (s := WindowTwentyOneTable.framed template (UInt256.ofNat 2335) base modulus 16 ([base, exponent] ++ rest))
    (env.transfer rfl rfl) rfl hi'
  have hloop := steps_three paths template env base modulus exponent rest hrest hjump
  have hfinish := paths.finish.steps
    (s := WindowTwentyOneLoop.finishState template base modulus exponent rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneCore.run_finish template base modulus exponent rest hrest)
  exact ((ht.trans hinit).trans hloop).trans hfinish

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore
