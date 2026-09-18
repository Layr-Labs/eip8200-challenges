import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOneMsize

/-- The window loop is unrolled in this image, so the three passes are three
distinct straight-line regions and each needs its own block.  The body is the
same four-hundred-and-one-instruction program at all three pcs; the link between
consecutive passes is the same seventeen-instruction program at both of its. -/
structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  table : Block artifact fork 840 WindowTwentyOneTableBuild.program
  init : Block artifact fork 932 WindowTwentyOneInit.program
  entry : Block artifact fork 952 WindowTwentyOneLoop.entryProgram
  trampoline : Block artifact fork 952 WindowTwentyOneLoop.trampolineProgram
  body0 : Block artifact fork 970 (WindowTwentyOneLoop.bodyProgram (21 * 0))
  link0 : Block artifact fork 1413 WindowTwentyOneLoop.linkProgram
  body1 : Block artifact fork 1436 (WindowTwentyOneLoop.bodyProgram (21 * 1))
  link1 : Block artifact fork 1879 WindowTwentyOneLoop.linkProgramB
  body2 : Block artifact fork 1902 (WindowTwentyOneLoop.bodyProgramLast 42)
  finish : Block artifact fork 2345 WindowTwentyOneReturn.program

/-- The three unrolled passes, from the loop head at 952 to the return entry at
2345.  Pass 0 is entered through the trampoline at 952; passes 1 and 2 are
entered through the links at 1413 and 1879.  No instruction in the chain is a
jump. -/
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
      (WindowTwentyOneLoop.headState template (UInt256.ofNat 970) base modulus exponent 0 rest) :=
    Block.stepsX paths.trampoline
      (s := WindowTwentyOneLoop.entryState template base modulus exponent rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_trampoline template base modulus exponent rest hrest)
  have b0 : GasSteps (WindowTwentyOneLoop.headState template (UInt256.ofNat 970) base modulus exponent 0 rest)
      (WindowTwentyOneLoop.postState template (UInt256.ofNat 1413) base modulus exponent 0 rest) :=
    paths.body0.steps
      (s := WindowTwentyOneLoop.headState template (UInt256.ofNat 970) base modulus exponent 0 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_body template 970 base modulus exponent 0 (by decide) rest hrest)
  have l0 : GasSteps (WindowTwentyOneLoop.postState template (UInt256.ofNat 1413) base modulus exponent 0 rest)
      (WindowTwentyOneLoop.headState template (UInt256.ofNat 1436) base modulus exponent 1 rest) :=
    paths.link0.steps
      (s := WindowTwentyOneLoop.postState template (UInt256.ofNat 1413) base modulus exponent 0 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_link template 1413 base modulus exponent 0 (by decide) rest hrest)
  have b1 : GasSteps (WindowTwentyOneLoop.headState template (UInt256.ofNat 1436) base modulus exponent 1 rest)
      (WindowTwentyOneLoop.postState template (UInt256.ofNat 1879) base modulus exponent 1 rest) :=
    paths.body1.steps
      (s := WindowTwentyOneLoop.headState template (UInt256.ofNat 1436) base modulus exponent 1 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_body template 1436 base modulus exponent 1 (by decide) rest hrest)
  have l1 : GasSteps (WindowTwentyOneLoop.postState template (UInt256.ofNat 1879) base modulus exponent 1 rest)
      (WindowTwentyOneLoop.headState template (UInt256.ofNat 1902) base modulus exponent 2 rest) :=
    paths.link1.steps
      (s := WindowTwentyOneLoop.postState template (UInt256.ofNat 1879) base modulus exponent 1 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_linkB template 1879 base modulus exponent 1 (by decide) rest hrest)
  have b2 : GasSteps (WindowTwentyOneLoop.headState template (UInt256.ofNat 1902) base modulus exponent 2 rest)
      (WindowTwentyOneLoop.finishState template base modulus exponent rest) :=
    paths.body2.steps
      (s := WindowTwentyOneLoop.headState template (UInt256.ofNat 1902) base modulus exponent 2 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_bodyLast template 1902 base modulus exponent rest hrest)
  exact ((((((e0.trans t0).trans b0).trans l0).trans b1).trans l1).trans b2)

/-- Table, init, three bodies and the return, from the normalized state at 840.
The exponent word and the spare modulus copy are read from the route frame. -/
def steps_core {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (he : rest[1]? = some exponent) (hm : rest[0]? = some modulus) :
    GasSteps (WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 840) base modulus rest)
      (WindowTwentyOneCore.returnedState template base modulus exponent rest) := by
  have ht := Block.stepsX paths.table
    (s := WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 840) base modulus rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneTableBuild.run_all template base modulus exponent rest hrest he)
  have hi := WindowTwentyOneInit.run_enter template base modulus exponent rest hrest hm
  have hi' : runInstructions WindowTwentyOneInit.program
      (WindowTwentyOneTable.framed template (UInt256.ofNat 932) base modulus 16 ([base, exponent] ++ rest)) =
      some (WindowTwentyOneLoop.entryState template base modulus exponent rest) := by
    simpa only [WindowTwentyOneLoop.entryState, WindowTwentyOneLoop.eAt,
      WindowTwentyOneLoop.spare,
      WindowTwentyOneMath.accumulator, WindowTwentyOneMath.advance] using hi
  have hinit := paths.init.steps
    (s := WindowTwentyOneTable.framed template (UInt256.ofNat 932) base modulus 16 ([base, exponent] ++ rest))
    (env.transfer rfl rfl) rfl hi'
  have hloop := steps_three paths template env base modulus exponent rest hrest
  have hfinish := paths.finish.steps
    (s := WindowTwentyOneLoop.finishState template base modulus exponent rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneCore.run_finish template base modulus exponent rest hrest)
  exact ((ht.trans hinit).trans hloop).trans hfinish

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore
