import Challenge.Ripemd160.Submission.Proofs.Bytecode.GasCost
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionEntryPrelude
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Loop
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Return

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Correct
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof

theorem of_returned (input : ByteArray) (t : State)
    (trace : GasSteps (initialState submissionBytecode input 0) t)
    (hhalt : t.halt = .Returned) (hcall : t.callStack = [])
    (hout : t.hReturn = spec input) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, State.isDone, State.isHalted, State.isRunning, hhalt, hcall])
  rw [State.toResult_returned _ (by simpa [withGas] using hhalt)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned t.hReturn) at heval
  rw [hout] at heval
  simpa [GasCost.withGas_initialState_zero] using heval

theorem from_entry (input : ByteArray)
    (hn : RecognitionAccumulator.Allowed input.size)
    (hentry : GasSteps (initialState submissionBytecode input 0) (PatternedScan.patternedEntry input))
    (hgeneric : ∀ rho : List UInt256, rho.length ≤ 20 →
      GasSteps (initialState submissionBytecode input 0)
        (J2Moves.atState (initialState submissionBytecode input 0) 340 rho) →
      ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
        Eval (initialState submissionBytecode input gas) (.returned (spec input))) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let s := initialState submissionBytecode input 0
  have e : J2Sites.Env s := ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩
  by_cases hz : J2Accumulator.resultAcc input input.size = 0
  · let rho := J2Raw.finishRest (J2End.endFrame s input.size) []
    have hc : rho.length ≤ 990 := by simp [rho, J2Raw.finishRest]
    have gh := J2Loop.gasSteps_hit s [] (J2Sites.moves s e [] (by decide)) input.size hn rfl hz
    have gr := J2Return.gasSteps s e rho hc rfl rfl
    have trace : GasSteps (initialState submissionBytecode input 0) (J2Return.output s rho) :=
      hentry.trans (gh.trans gr)
    exact of_returned input _ trace (J2Return.output_halt s rho) rfl
      (J2Return.output_spec s e rho hn hz)
  · have gm := J2Loop.gasSteps_miss s [] (J2Sites.moves s e [] (by decide)) input.size hn rfl hz
    have ge := J2Sites.gasSteps_generic_entry s e
      (J2Raw.finishRest (J2End.endFrame s input.size) []) (by simp [J2Raw.finishRest])
    exact hgeneric _ (by simp [J2Raw.finishRest]) (hentry.trans (gm.trans ge))

#print axioms of_returned
#print axioms from_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Correct
