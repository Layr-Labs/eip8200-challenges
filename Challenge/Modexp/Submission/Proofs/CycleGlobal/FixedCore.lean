import Challenge.Modexp.Submission.Proofs.CycleGlobal.FixedDispatch
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 3000000
namespace CycleSubmission.FixedCore
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.EvmProof WindowTwentyOneBinding WindowTwentyOnePositive WindowNibbleKernel
open CycleSubmission.FixedDispatch

def entryState (template : State) (input : ByteArray) (tail : List UInt256) : State :=
  { WindowTwentyOneGasRoute.entryState template input tail with pc := UInt256.ofNat 10943 }
structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  guard : Block artifact fork 10943 guardProgram
  body : Block artifact fork 10983 HistoricalSearch.FixedExponentProgram.program
  oldJump : Decode.isValidJumpDest artifact.code 717 = true

theorem handled {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (legacy : WindowTwentyOneGasRoute.Paths artifact fork)
    (template : State) (env : Environment artifact fork template) (hcall : template.callStack = [])
    (input : ByteArray) (tail : List UInt256) (htail : tail.length ≤ 590)
    (hmatch : WindowTwentyOneInput.Matches input) :
    ∃ final : State, Nonempty (GasSteps (entryState template input tail) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ctx := context template input
  let m := WindowTwentyOneInput.modulusWord input
  let e := WindowTwentyOneInput.exponentWord input
  let b := WindowTwentyOneInput.baseWord input
  have ec := WindowTwentyOneGasRoute.context_env template env input
  have hj : Decode.isValidJumpDest ctx.executionEnv.code 717 = true := by
    rw [ec.code]
    exact paths.oldJump
  have hg := run_guard ctx m e b tail htail ec.running hj
  by_cases he : (UInt256.xor exponent e).toNat = 0
  · rw [if_pos he] at hg
    have gs : GasSteps (entryState template input tail) (frame ctx 10983 m e b tail) :=
      paths.guard.steps (ec.transfer rfl rfl) rfl hg
    have hr := HistoricalSearch.FixedExponentProgram.run_program ctx (UInt256.ofNat 10983)
      b m e tail htail
    have hr' : runInstructions HistoricalSearch.FixedExponentProgram.program
        (frame ctx 10983 m e b tail) =
        some (HistoricalSearch.FixedExponentProgram.finalState ctx (UInt256.ofNat 10983) b m e tail) := by
      simpa only [frame, HistoricalSearch.FixedExponentBlocks.framed, ctx, context] using hr
    have bs : GasSteps (frame ctx 10983 m e b tail)
        (HistoricalSearch.FixedExponentProgram.finalState ctx (UInt256.ofNat 10983) b m e tail) :=
      paths.body.steps (ec.transfer rfl rfl) rfl hr'
    refine ⟨HistoricalSearch.FixedExponentProgram.finalState ctx (UInt256.ofNat 10983) b m e tail,
      ⟨gs.trans bs⟩, ?_, ?_⟩
    · change (true && template.callStack.isEmpty) = true
      rw [hcall]
      rfl
    · rw [HistoricalSearch.FixedExponentProgram.finalState, WindowTwentyOneReturn.returned_result]
      exact congrArg ExecutionResult.returned (value_spec input hmatch ((xor_zero_iff e).mp he))
  · rw [if_neg he] at hg
    have gs : GasSteps (entryState template input tail)
        (WindowTwentyOneGasRoute.entryState template input tail) :=
      paths.guard.steps (ec.transfer rfl rfl) rfl hg
    obtain ⟨final, ⟨trace⟩, done, result⟩ :=
      WindowTwentyOneGasRoute.handled legacy template env hcall input tail htail hmatch
    exact ⟨final, ⟨gs.trans trace⟩, done, result⟩
end CycleSubmission.FixedCore
