import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Core
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
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Correct
