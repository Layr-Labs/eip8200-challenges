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
  init : Block artifact fork 968 WindowTwentyOneInit.program
  trampoline : Block artifact fork 979 WindowTwentyOneLoop.trampolineProgram
  entry : Block artifact fork 984 WindowTwentyOneLoop.entryProgram
  body0 : Block artifact fork 994 (WindowTwentyOneLoop.bodyProgram (16 * 0))
  body1 : Block artifact fork 1345 (WindowTwentyOneLoop.bodyProgram (16 * 1))
  body2 : Block artifact fork 1696 (WindowTwentyOneLoop.bodyProgram (16 * 2))
  bodyLast : Block artifact fork 2047 (WindowTwentyOneLoop.bodyProgramLast 48)
  finish : Block artifact fork 2374 WindowTwentyOneReturn.program

/-- From the setup frame at 979: the exponent copies, the first-digit lookup,
three full blocks and the last block. -/
def steps_three {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256) (rest : List UInt256) (hrest : rest.length ≤ 999) :
    GasSteps (WindowTwentyOneLoop.entryState template base modulus exponent rest)
      (WindowTwentyOneLoop.finishState template base modulus exponent rest) := by
  have t0 : GasSteps (WindowTwentyOneLoop.entryState template base modulus exponent rest)
      (WindowTwentyOneLoop.copiedState template base modulus exponent rest) :=
    Block.stepsX paths.trampoline
      (s := WindowTwentyOneLoop.entryState template base modulus exponent rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_trampoline template base modulus exponent rest hrest)
  have e0 : GasSteps (WindowTwentyOneLoop.copiedState template base modulus exponent rest)
      (WindowTwentyOneLoop.headState template (UInt256.ofNat 994) base modulus exponent 0 rest) :=
    paths.entry.steps (s := WindowTwentyOneLoop.copiedState template base modulus exponent rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_entry template base modulus exponent rest hrest)
  have b0 : GasSteps (WindowTwentyOneLoop.headState template (UInt256.ofNat 994) base modulus exponent 0 rest)
      (WindowTwentyOneLoop.headState template (UInt256.ofNat 1345) base modulus exponent 1 rest) :=
    paths.body0.steps
      (s := WindowTwentyOneLoop.headState template (UInt256.ofNat 994) base modulus exponent 0 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_body template 994 base modulus exponent 0 (by decide) rest hrest)
  have b1 : GasSteps (WindowTwentyOneLoop.headState template (UInt256.ofNat 1345) base modulus exponent 1 rest)
      (WindowTwentyOneLoop.headState template (UInt256.ofNat 1696) base modulus exponent 2 rest) :=
    paths.body1.steps
      (s := WindowTwentyOneLoop.headState template (UInt256.ofNat 1345) base modulus exponent 1 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_body template 1345 base modulus exponent 1 (by decide) rest hrest)
  have b2 : GasSteps (WindowTwentyOneLoop.headState template (UInt256.ofNat 1696) base modulus exponent 2 rest)
      (WindowTwentyOneLoop.headState template (UInt256.ofNat 2047) base modulus exponent 3 rest) :=
    paths.body2.steps
      (s := WindowTwentyOneLoop.headState template (UInt256.ofNat 1696) base modulus exponent 2 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_body template 1696 base modulus exponent 2 (by decide) rest hrest)
  have last : GasSteps (WindowTwentyOneLoop.headState template (UInt256.ofNat 2047) base modulus exponent 3 rest)
      (WindowTwentyOneLoop.finishState template base modulus exponent rest) :=
    paths.bodyLast.steps
      (s := WindowTwentyOneLoop.headState template (UInt256.ofNat 2047) base modulus exponent 3 rest)
      (env.transfer rfl rfl) rfl
      (WindowTwentyOneLoop.run_bodyLast template 2047 base modulus exponent rest hrest)
  exact ((((t0.trans e0).trans b0).trans b1).trans b2).trans last

/-- Table, setup, copies, lookup, four blocks and the return, from the
normalized state at 879.  The exponent word and the spare modulus copy are read
from the route frame and stay in place under the ladder's mask. -/
def steps_core {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (he : rest[1]? = some exponent) (hm : rest[0]? = some modulus) :
    GasSteps (WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 879) base modulus rest)
      (WindowTwentyOneCore.returnedState template base modulus exponent (rest.drop 2)) := by
  have ht := Block.stepsX paths.table
    (s := WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 879) base modulus rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneTableBuild.run_all template base modulus exponent rest hrest he)
  have hrest_eq : rest = [modulus, exponent] ++ rest.drop 2 := by
    rcases rest with _ | ⟨x0, _ | ⟨x1, tail⟩⟩
    · simp at hm
    · simp at he
    · simp only [List.getElem?_cons_zero] at hm
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at he
      cases hm; cases he; rfl
  have hdrop_len : (rest.drop 2).length ≤ 999 := by simp [List.length_drop]; omega
  have hdrop_len' : (rest.drop 2).length ≤ 1000 := by omega
  have hi := WindowTwentyOneInit.run_enter template base modulus exponent (rest.drop 2) hdrop_len'
  have hi' : runInstructions WindowTwentyOneInit.program
      (WindowTwentyOneTable.framed template (UInt256.ofNat 968) base modulus 16 rest) =
      some (WindowTwentyOneLoop.entryState template base modulus exponent (rest.drop 2)) := by
    rw [← hrest_eq] at hi
    simpa only [WindowTwentyOneLoop.entryState] using hi
  have hinit := paths.init.steps
    (s := WindowTwentyOneTable.framed template (UInt256.ofNat 968) base modulus 16 rest)
    (env.transfer rfl rfl) rfl hi'
  have hloop := steps_three paths template env base modulus exponent (rest.drop 2) hdrop_len
  have hfinish := paths.finish.steps
    (s := WindowTwentyOneLoop.finishState template base modulus exponent (rest.drop 2))
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneCore.run_finish template base modulus exponent (rest.drop 2) hdrop_len')
  exact ((ht.trans hinit).trans hloop).trans hfinish

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore
