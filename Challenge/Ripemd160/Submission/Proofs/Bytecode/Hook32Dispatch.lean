import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32ReturnTrace

set_option warningAsError true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Dispatch
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Shared32Sites Hook32Return

private theorem eval_returned (input : ByteArray) (t : State)
    (trace : GasSteps (initialState submissionBytecode input 0) t)
    (hr : t.halt = .Returned) (hc : t.callStack = []) (hb : t.hReturn = spec input) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have he := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, State.isDone, State.isHalted, State.isRunning, hc, hr])
  rw [State.toResult_returned _ (by simpa [withGas] using hr)] at he
  change Eval (withGas (initialState submissionBytecode input 0) gas) (.returned t.hReturn) at he
  simpa only [GasCost.withGas_initialState_zero, hb] using he

/-- Size-32 dispatch is total: each exact word returns its certified digest;
only the three-word miss continues along the generic hash path. -/
theorem correct (input : ByteArray) (hsize : input.size = 32)
    (s : State) (e : Env s) (stk : List UInt256) (hlen : stk.length + 3 < 1024)
    (hinput : s.executionEnv.calldata = input) (hc : s.callStack = [])
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (atState s 160 ((1 : UInt256) :: stk)))
    (miss : MachineState.readWord input 0 ≠ Hook32.word0 →
      MachineState.readWord input 0 ≠ Hook32.word1 →
      MachineState.readWord input 0 ≠ Hook32.word2 →
      ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
        Eval (initialState submissionBytecode input gas) (.returned (spec input))) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  have g0 := entryPrefix.trans (Hook32Route.gas_enter s e stk hlen)
  by_cases h0 : MachineState.readWord input 0 = Hook32.word0
  · have gh := Hook32Hit.gas_cmp0_hit s e stk (by simpa only [hinput] using h0) hlen
    have gr := Hook32ReturnTrace.hit0.gas_stub s e stk (by omega)
    exact eval_returned input (returned s stk push0 9819)
      (g0.trans (gh.trans gr)) rfl hc
      (by simpa only [hinput] using (Hook32ReturnTrace.hit0.returns_spec s stk
        (by simpa only [hinput] using hsize) (by simpa only [hinput] using h0)))
  have g1 := g0.trans (Hook32.gas_cmp0 s e stk (by simpa only [hinput] using h0) hlen)
  by_cases h1 : MachineState.readWord input 0 = Hook32.word1
  · have gh := Hook32Hit.gas_cmp1_hit s e stk (by simpa only [hinput] using h1) hlen
    have gr := Hook32ReturnTrace.hit1.gas_stub s e stk (by omega)
    exact eval_returned input (returned s stk push1 9847)
      (g1.trans (gh.trans gr)) rfl hc
      (by simpa only [hinput] using (Hook32ReturnTrace.hit1.returns_spec s stk
        (by simpa only [hinput] using hsize) (by simpa only [hinput] using h1)))
  have g2 := g1.trans (Hook32.gas_cmp1 s e stk (by simpa only [hinput] using h1) hlen)
  by_cases h2 : MachineState.readWord input 0 = Hook32.word2
  · have gh := Hook32Hit.gas_cmp2_hit s e stk (by simpa only [hinput] using h2) hlen
    have gr := Hook32ReturnTrace.hit2.gas_stub s e stk (by omega)
    exact eval_returned input (returned s stk push2 9875)
      (g2.trans (gh.trans gr)) rfl hc
      (by simpa only [hinput] using (Hook32ReturnTrace.hit2.returns_spec s stk
        (by simpa only [hinput] using hsize) (by simpa only [hinput] using h2)))
  exact miss h0 h1 h2
#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Dispatch
