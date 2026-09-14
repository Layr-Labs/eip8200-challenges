import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Core
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Start
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GasCost
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Correct
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof

/-- Keep the gas trace abstract while connecting its terminal state to the evaluator. -/
theorem eval_of_returned_trace (s t : State) (output : ByteArray)
    (trace : GasSteps s t) (hr : t.halt = .Returned) (hc : t.callStack = [])
    (hb : t.hReturn = output) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas → Eval (withGas s gas) (.returned output) := by
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have he := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, State.isDone, State.isHalted, State.isRunning, hc, hr])
  rw [State.toResult_returned _ (by exact hr)] at he
  change Eval (withGas s gas) (.returned t.hReturn) at he
  rw [hb] at he
  exact he

/-- The abstract returned-trace lemma specialized only at the challenge's initial state. -/
theorem eval_of_initial_returned (input : ByteArray) (t : State)
    (trace : GasSteps (initialState submissionBytecode input 0) t)
    (hr : t.halt = .Returned) (hc : t.callStack = []) (hb : t.hReturn = spec input) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  obtain ⟨g₀, hg⟩ := eval_of_returned_trace (initialState submissionBytecode input 0)
    t (spec input) trace hr hc hb
  exact ⟨g₀, fun gas hgas => by
    simpa only [GasCost.withGas_initialState_zero] using hg gas hgas⟩

#print axioms eval_of_returned_trace
#print axioms eval_of_initial_returned

/-- Return state of the complete exact32 route. -/
def resultState (input : ByteArray) : State :=
  Shared32Core.resultState (Shared32Start.tableState input)

def gasSteps (input : ByteArray) (h32 : input.size = 32)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 352)) :
    GasSteps (initialState submissionBytecode input 0) (resultState input) := by
  let s := Shared32Start.tableState input
  have e : Shared32Sites.Env s := ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩
  have gs := Shared32Start.gasSteps input h32 entryPrefix
  have gc := Shared32Core.gasSteps s e input rfl h32 (Shared32Start.copied_active input h32)
  exact gs.trans gc

/-- Exact32 correctness uses an opaque generic trace-to-evaluation bridge. -/
theorem correct (input : ByteArray) (h32 : input.size = 32)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 352)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  exact eval_of_initial_returned input (resultState input) (gasSteps input h32 entryPrefix)
    (Shared32Core.resultState_halt _) (by rfl)
    (Shared32Core.returned_spec _ input h32 (Shared32Start.table_ready input h32))

#print axioms gasSteps
#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Correct
