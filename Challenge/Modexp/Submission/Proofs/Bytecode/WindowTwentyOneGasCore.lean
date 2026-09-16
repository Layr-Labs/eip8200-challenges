import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOneMsize

structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  table : Block artifact fork 1408 WindowTwentyOneTableBuild.program
  init : Block artifact fork 1503 WindowTwentyOneInit.program
  entry : Block artifact fork 1519 WindowTwentyOneLoop.entryProgram
  trampoline : Block artifact fork 1519 WindowTwentyOneLoop.trampolineProgram
  body : Block artifact fork 1538 WindowTwentyOneLoop.bodyProgram
  finish : Block artifact fork 1995 WindowTwentyOneReturn.program

/-- One trampoline pass: store the copies, run the body, jump back to the trampoline. -/
def steps_pass {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256) (count : Nat) (hcount : count < 2)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htramp : Decode.isValidJumpDest template.executionEnv.code 1519 = true) :
    GasSteps (WindowTwentyOneLoop.loopState template base modulus exponent count rest)
      (WindowTwentyOneLoop.loopState template base modulus exponent (count + 1) rest) :=
  (paths.trampoline.steps
    (s := WindowTwentyOneLoop.loopState template base modulus exponent count rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneLoop.run_trampoline template base modulus exponent count rest hrest)).trans
  (paths.body.steps
    (s := WindowTwentyOneLoop.headState template base modulus exponent count rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneLoop.run_continue template base modulus exponent count hcount rest hrest htramp))

def steps_three {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256) (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htramp : Decode.isValidJumpDest template.executionEnv.code 1519 = true) :
    GasSteps (WindowTwentyOneLoop.entryState template base modulus exponent rest)
      (WindowTwentyOneLoop.finishState template base modulus exponent rest) :=
  (((paths.entry.steps
    (s := WindowTwentyOneLoop.entryState template base modulus exponent rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneLoop.run_entry template base modulus exponent rest hrest htramp)).trans
  (steps_pass paths template env base modulus exponent 0 (by decide) rest hrest htramp)).trans
  (steps_pass paths template env base modulus exponent 1 (by decide) rest hrest htramp)).trans
  ((paths.trampoline.steps
    (s := WindowTwentyOneLoop.loopState template base modulus exponent 2 rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneLoop.run_trampoline template base modulus exponent 2 rest hrest)).trans
  (paths.body.steps
    (s := WindowTwentyOneLoop.headState template base modulus exponent 2 rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneLoop.run_last template base modulus exponent rest hrest htramp)))

/-- Table, init, three bodies and the return, from the normalized state at 1792.
The exponent word and the spare modulus copy are read from the route frame. -/
def steps_core {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (he : rest[1]? = some exponent) (hm : rest[0]? = some modulus)
    (htramp : Decode.isValidJumpDest template.executionEnv.code 1519 = true) :
    GasSteps (WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 1408) base modulus rest)
      (WindowTwentyOneCore.returnedState template base modulus exponent rest) := by
  have ht := Block.stepsX paths.table
    (s := WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 1408) base modulus rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneTableBuild.run_all template base modulus exponent rest hrest he)
  have hi := WindowTwentyOneInit.run_enter template base modulus exponent rest hrest hm
  have hi' : runInstructions WindowTwentyOneInit.program
      (WindowTwentyOneTable.framed template (UInt256.ofNat 1503) base modulus 16
        ([UInt256.ofNat 480, exponent] ++ rest)) =
      some (WindowTwentyOneLoop.entryState template base modulus exponent rest) := by
    simpa only [WindowTwentyOneLoop.entryState, WindowTwentyOneLoop.eAt,
      WindowTwentyOneMath.accumulator, WindowTwentyOneMath.advance] using hi
  have hinit := paths.init.steps
    (s := WindowTwentyOneTable.framed template (UInt256.ofNat 1503) base modulus 16
      ([UInt256.ofNat 480, exponent] ++ rest))
    (env.transfer rfl rfl) rfl hi'
  have hloop := steps_three paths template env base modulus exponent rest hrest htramp
  have hfinish := paths.finish.steps
    (s := WindowTwentyOneLoop.finishState template base modulus exponent rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneCore.run_finish template base modulus exponent rest hrest)
  exact ((ht.trans hinit).trans hloop).trans hfinish

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore
