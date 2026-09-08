import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineBinding

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineGasCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof WindowNibbleKernel WindowNineBinding

structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  table : Block artifact fork 3044 WindowNineTableBuild.program
  init : Block artifact fork 3161 WindowNineInit.program
  iteration : Block artifact fork 3183 WindowNineLoop.iterationProgram
  finish : Block artifact fork 3390 WindowNineReturn.program

def steps_continue {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256) (count : Nat) (hcount : count < 6)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 3183 = true) :
    GasSteps (WindowNineLoop.loopState template base modulus exponent count rest)
      (WindowNineLoop.loopState template base modulus exponent (count + 1) rest) :=
  paths.iteration.steps (env.transfer rfl rfl) rfl
    (WindowNineLoop.run_continue template base modulus exponent count hcount rest hrest hjump)

def steps_prefix {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256) (count : Nat) (hcount : count ≤ 6)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 3183 = true) :
    GasSteps (WindowNineLoop.loopState template base modulus exponent 0 rest)
      (WindowNineLoop.loopState template base modulus exponent count rest) := by
  induction count with
  | zero => exact GasSteps.refl _
  | succ count ih =>
      exact (ih (by omega)).trans
        (steps_continue paths template env base modulus exponent count (by omega) rest hrest hjump)

def steps_seven {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256) (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 3183 = true) :
    GasSteps (WindowNineLoop.loopState template base modulus exponent 0 rest)
      (WindowNineLoop.finishState template base modulus exponent rest) :=
  (steps_prefix paths template env base modulus exponent 6 (by decide) rest hrest hjump).trans
    (paths.iteration.steps (env.transfer rfl rfl) rfl
      (WindowNineLoop.run_last template base modulus exponent rest hrest hjump))

def steps_core {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponentOffset modulusOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (he : rest[4]? = some exponentOffset) (hm : rest[5]? = some modulusOffset)
    (hmodulus : MachineState.readWord template.executionEnv.calldata modulusOffset.toNat = modulus)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 3183 = true) :
    GasSteps (WindowNineTablePrelude.initial template (UInt256.ofNat 3044) base modulus rest)
      (WindowNineCore.returnedState template base modulus
        (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat) rest) := by
  let exponent := MachineState.readWord template.executionEnv.calldata exponentOffset.toNat
  have ht := paths.table.steps
    (s := WindowNineTablePrelude.initial template (UInt256.ofNat 3044) base modulus rest)
    (env.transfer rfl rfl) rfl
    (WindowNineTableBuild.run_all template base modulus exponentOffset rest hrest he)
  have hi := WindowNineInit.run_enter template base modulus exponent modulusOffset rest hrest hm hmodulus
  have hi' : runInstructions WindowNineInit.program
      (WindowNineTable.state template (UInt256.ofNat 3161) base modulus exponent 15 rest) =
      some (WindowNineLoop.loopState template base modulus exponent 0 rest) := by
    simpa only [WindowNineLoop.loopState, WindowNineMath.accumulator, WindowNineMath.advance] using hi
  have hinit := paths.init.steps
    (s := WindowNineTable.state template (UInt256.ofNat 3161) base modulus exponent 15 rest)
    (env.transfer rfl rfl) rfl hi'
  have hloop := steps_seven paths template env base modulus exponent rest hrest hjump
  have hfinish := paths.finish.steps
    (s := WindowNineLoop.finishState template base modulus exponent rest)
    (env.transfer rfl rfl) rfl
    (WindowNineCore.run_finish template base modulus exponent rest hrest)
  exact ((ht.trans hinit).trans hloop).trans hfinish

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineGasCore
