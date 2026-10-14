import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOneMsize

/-- The precopy route: table, setup, row stores, the modulus pool, the first digit,
sixty windows and the tail with the return. -/
structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  table : Block artifact fork 820 WindowTwentyOneTableBuild.program
  setup : Block artifact fork 909 WindowPrecopyRoute.setupProgram
  copy : Block artifact fork 917 WindowPrecopyRoute.copyProgram
  pool : Block artifact fork 922 WindowPrecopyRoute.poolProgram
  first : Block artifact fork 1237 WindowPrecopyRoute.firstProgram
  head : Block artifact fork 1249 (WindowPrecopyRoute.routeWindows 0 60)
  tail : Block artifact fork 2329 WindowPrecopyRoute.tailProgram

/-- Table, setup, row stores, pool, first digit, 62 windows, the last digit and the
return, from the normalized state at 879.  The exponent word and the spare modulus
copy are read from the route frame and stay in place under the pool. -/
def steps_core {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600)
    (he : rest[1]? = some exponent) (hm : rest[0]? = some modulus) :
    GasSteps (WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 820) base modulus rest)
      (WindowTwentyOneCore.returnedState template base modulus exponent (rest.drop 2)) := by
  have ht := Block.stepsX paths.table
    (s := WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 820) base modulus rest)
    (env.transfer rfl rfl) rfl
    (WindowTwentyOneTableBuild.run_all template base modulus exponent rest (by omega) he)
  have hrest_eq : rest = modulus :: exponent :: rest.drop 2 := by
    rcases rest with _ | ⟨x0, _ | ⟨x1, tail⟩⟩
    · simp at hm
    · simp at he
    · simp only [List.getElem?_cons_zero] at hm
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at he
      cases hm; cases he; rfl
  have hdrop : (rest.drop 2).length ≤ 600 := by simp [List.length_drop]; omega
  have hs := WindowPrecopyRoute.run_setupAt template base modulus exponent (rest.drop 2) hdrop
  rw [← hrest_eq] at hs
  have gs := paths.setup.steps
    (s := WindowTwentyOneTable.framed template (UInt256.ofNat 909) base modulus 16 rest)
    (env.transfer rfl rfl) rfl hs
  have gc := Block.stepsX paths.copy
    (s := WindowTwentyOneTable.framed template (UInt256.ofNat 917) base modulus 16
      (UInt256.shiftRight exponent (UInt256.ofNat 3) ::
        WindowPrecopyRoute.frame modulus exponent (rest.drop 2)))
    (env.transfer rfl rfl) rfl
    (WindowPrecopyRoute.run_copyAt template base modulus exponent (rest.drop 2) hdrop)
  have gp := paths.pool.steps
    (s := WindowPrecopyRoute.routeState template 922 base modulus exponent
      (WindowPrecopyRoute.frame modulus exponent (rest.drop 2)))
    (env.transfer rfl rfl) rfl
    (WindowPrecopyRoute.run_poolAt template base modulus exponent (rest.drop 2) hdrop)
  have gf := paths.first.steps
    (s := WindowPrecopyRoute.routeState template 1237 base modulus exponent
      (List.replicate 315 modulus ++ WindowPrecopyRoute.frame modulus exponent (rest.drop 2)))
    (env.transfer rfl rfl) rfl
    (WindowPrecopyRoute.run_firstAt template base modulus exponent (rest.drop 2) hdrop)
  have gh := paths.head.steps
    (s := WindowPrecopyRoute.routeState template 1249 base modulus exponent
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat ::
        List.replicate 315 modulus ++ WindowPrecopyRoute.frame modulus exponent (rest.drop 2)))
    (env.transfer rfl rfl) rfl
    (WindowPrecopyRoute.run_headAt template base modulus exponent (rest.drop 2) hdrop)
  have gt := paths.tail.steps
    (s := WindowPrecopyRoute.routeState template 2329 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60 ::
        List.replicate 15 modulus ++ WindowPrecopyRoute.frame modulus exponent (rest.drop 2)))
    (env.transfer rfl rfl) rfl
    (WindowPrecopyRoute.run_tailAt template base modulus exponent (rest.drop 2) hdrop)
  exact (((((ht.trans gs).trans gc).trans gp).trans gf).trans gh).trans gt

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore
