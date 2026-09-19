import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOneMsize

/-- Three sixteen-digit blocks followed by the final fifteen-digit block. -/
structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  table : Block artifact fork 879 WindowTwentyOneTableBuild.program
  init : Block artifact fork 971 WindowTwentyOneInit.program
  entry : Block artifact fork 988 WindowTwentyOneLoop.entryProgram
  trampoline : Block artifact fork 988 WindowTwentyOneLoop.trampolineProgram
  body0 : Block artifact fork 997 (WindowTwentyOneLoop.bodyProgram (16 * 0))
  body1 : Block artifact fork 1348 (WindowTwentyOneLoop.bodyProgram (16 * 1))
  body2 : Block artifact fork 1699 (WindowTwentyOneLoop.bodyProgram (16 * 2))
  bodyLast : Block artifact fork 2050 (WindowTwentyOneLoop.bodyProgramLast 48)
  finish : Block artifact fork 2377 WindowTwentyOneReturn.program

def steps_three {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256) (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    GasSteps (WindowTwentyOneLoop.entryState template base modulus exponent rest)
      (WindowTwentyOneLoop.finishState template base modulus exponent rest) := by
  have e0 : GasSteps (WindowTwentyOneLoop.entryState template base modulus exponent rest)
      (WindowTwentyOneLoop.entryState template base modulus exponent rest) :=
    paths.entry.steps (s := WindowTwentyOneLoop.entryState template base modulus exponent rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_entry template base modulus exponent rest hrest)
  have t0 : GasSteps (WindowTwentyOneLoop.entryState template base modulus exponent rest)
      (WindowTwentyOneLoop.headState template (UInt256.ofNat 997) base modulus exponent 0 rest) :=
    Block.stepsX paths.trampoline
      (s := WindowTwentyOneLoop.entryState template base modulus exponent rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_trampoline template base modulus exponent rest hrest)
  have b0 : GasSteps (WindowTwentyOneLoop.headState template (UInt256.ofNat 997) base modulus exponent 0 rest)
      (WindowTwentyOneLoop.headState template (UInt256.ofNat 1348) base modulus exponent 1 rest) :=
    paths.body0.steps
      (s := WindowTwentyOneLoop.headState template (UInt256.ofNat 997) base modulus exponent 0 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_body template 997 base modulus exponent 0 (by decide) rest hrest)
  have b1 : GasSteps (WindowTwentyOneLoop.headState template (UInt256.ofNat 1348) base modulus exponent 1 rest)
      (WindowTwentyOneLoop.headState template (UInt256.ofNat 1699) base modulus exponent 2 rest) :=
    paths.body1.steps
      (s := WindowTwentyOneLoop.headState template (UInt256.ofNat 1348) base modulus exponent 1 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_body template 1348 base modulus exponent 1 (by decide) rest hrest)
  have b2 : GasSteps (WindowTwentyOneLoop.headState template (UInt256.ofNat 1699) base modulus exponent 2 rest)
      (WindowTwentyOneLoop.headState template (UInt256.ofNat 2050) base modulus exponent 3 rest) :=
    paths.body2.steps
      (s := WindowTwentyOneLoop.headState template (UInt256.ofNat 1699) base modulus exponent 2 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_body template 1699 base modulus exponent 2 (by decide) rest hrest)
  have last : GasSteps (WindowTwentyOneLoop.headState template (UInt256.ofNat 2050) base modulus exponent 3 rest)
      (WindowTwentyOneLoop.finishState template base modulus exponent rest) :=
    paths.bodyLast.steps
      (s := WindowTwentyOneLoop.headState template (UInt256.ofNat 2050) base modulus exponent 3 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_bodyLast template 2050 base modulus exponent rest hrest)
  exact ((((e0.trans t0).trans b0).trans b1).trans b2).trans last

/-- Table, init, four blocks and the return, from the normalized state at 879.
The exponent word and the spare modulus copy are read from the route frame. -/
def steps_core {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (he : rest[1]? = some exponent) (hm : rest[0]? = some modulus) :
    GasSteps (WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 879) base modulus rest)
      (WindowTwentyOneCore.returnedState template base modulus exponent rest) := by
  have ht := Block.stepsX paths.table
    (s := WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 879) base modulus rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneTableBuild.run_all template base modulus exponent rest hrest he)
  have hi := WindowTwentyOneInit.run_enter template base modulus exponent rest hrest hm
  have hi' : runInstructions WindowTwentyOneInit.program
      (WindowTwentyOneTable.framed template (UInt256.ofNat 971) base modulus 16 ([base, exponent] ++ rest)) =
      some (WindowTwentyOneLoop.entryState template base modulus exponent rest) := by
    simpa only [WindowTwentyOneLoop.entryState, WindowTwentyOneLoop.eAt,
      WindowTwentyOneLoop.spare,
      WindowTwentyOneMath.accumulator, WindowTwentyOneMath.advance] using hi
  have hinit := paths.init.steps
    (s := WindowTwentyOneTable.framed template (UInt256.ofNat 971) base modulus 16 ([base, exponent] ++ rest))
    (env.transfer rfl rfl) rfl hi'
  have hloop := steps_three paths template env base modulus exponent rest hrest
  have hfinish := paths.finish.steps
    (s := WindowTwentyOneLoop.finishState template base modulus exponent rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneCore.run_finish template base modulus exponent rest hrest)
  exact ((ht.trans hinit).trans hloop).trans hfinish

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore
