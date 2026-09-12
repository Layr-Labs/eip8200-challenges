import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionEntryPrelude
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionScan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionReturn

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect
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

theorem from_entry (input : ByteArray) (hfit : CalldataFits input)
    (hn : RecognitionAccumulator.Allowed input.size)
    (hentry : GasSteps (initialState submissionBytecode input 0) (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let s := initialState submissionBytecode input 0
  have e : RecognitionSites.Env s := ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩
  by_cases hz : RecognitionAccumulator.resultAcc input input.size = 0
  · let rho := RecognitionBodyRaw.frame (RecognitionLoop.endFrame s input.size) []
    have hc : rho.length ≤ 990 := by simp [rho, RecognitionBodyRaw.frame]
    have gh := RecognitionScan.gasSteps_hit s e input.size [] (by decide) hn rfl hz
    have gr := RecognitionReturn.gasSteps s e rho hc rfl rfl
    have trace : GasSteps (initialState submissionBytecode input 0) (RecognitionReturn.output s rho) :=
      hentry.trans (gh.trans gr)
    exact of_returned input _ trace (RecognitionReturn.output_halt s rho) rfl
      (RecognitionReturn.output_spec s e rho hn hz)
  · have gm := RecognitionScan.gasSteps_miss s e input.size [] (by decide) hn rfl hz
    exact StackCorrect.correct input hfit (RecognitionAccumulator.allowed_bounds input.size hn).1
      (hentry.trans gm)

#print axioms of_returned
#print axioms from_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect
