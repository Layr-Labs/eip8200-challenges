import Challenge.Ripemd160.Submission.Proofs.Bytecode.GasCost
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionEntryPrelude
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Loop
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Sites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EarlySerializeReturn
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EarlySerializeFallback

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

theorem from_entry (c : J2FusedSites.Certificates) (input : ByteArray)
    (hn : RecognitionAccumulator.Allowed input.size)
    (hfit : CalldataFits input)
    (hentry : GasSteps (initialState submissionBytecode input 0) (PatternedScan.patternedEntry input))
    (hgeneric : ∀ rho : List UInt256, rho.length ≤ 20 →
      GasSteps (initialState submissionBytecode input 0)
        (StackTail.append (PaddingTrace.padFramed input) rho) →
      ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
        Eval (initialState submissionBytecode input gas) (.returned (spec input))) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let saved : List UInt256 := [PatternedScan.segEnd input.size]
  let s := EarlySerializeReturn.prepared input saved
  have e : J2Sites.Env s := ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩
  have hactive : s.activeWords = UInt256.ofNat 1 := rfl
  have gprepare := EarlySerializeReturn.gasSteps_prepare input saved (by simp [saved])
  have gp : GasSteps (PatternedScan.patternedEntry input)
      (J2Moves.atState s 4618 [J2Raw.clamp (UInt256.ofNat input.size)]) := by
    exact GasSteps.cast gprepare rfl (by
      rw [EarlySerializeReturn.prepared_atState]
      rfl)
  have moves := J2Sites.moves c s e [] (by decide) hactive
  by_cases h256 : input.size = 256
  · by_cases hz : J2FusedAccumulator.resultAcc256 input = 0
    · let rho := J2FusedLoop.rest256 s []
      have hc : rho.length ≤ 990 := by simp [rho, J2FusedLoop.rest256, J2Raw.finishRest]
      have gr := J2FusedSites.gasSteps_return c input saved rho hc
      have gh := J2FusedCorrect.hit input saved moves h256 hz gr
      have trace : GasSteps (initialState submissionBytecode input 0)
          (J2FusedCorrect.output input rho) := hentry.trans (gp.trans gh)
      exact of_returned input _ trace (J2FusedCorrect.output_halt input rho) rfl
        (J2FusedCorrect.output_spec input rho h256 hz)
    · let rho := J2FusedLoop.rest256 s []
      have hc : rho.length ≤ 20 := by simp [rho, J2FusedLoop.rest256, J2Raw.finishRest]
      have gm := J2FusedCorrect.miss input saved hfit moves h256 hz
      exact hgeneric rho hc (hentry.trans (gp.trans gm))
  by_cases hz : J2Accumulator.resultAcc input input.size = 0
  · let rho := J2Raw.finishRest (J2End.endFrame s input.size) []
    have hc : rho.length ≤ 990 := by simp [rho, J2Raw.finishRest]
    have gh := J2Loop.gasSteps_hit s [] moves input.size hn rfl h256 hz
    have gr := EarlySerializeReturn.gasSteps_return input saved rho hc
    have trace : GasSteps (initialState submissionBytecode input 0)
        (EarlySerializeReturn.output input rho) :=
      hentry.trans (gp.trans (gh.trans gr))
    exact of_returned input _ trace (EarlySerializeReturn.output_halt input rho) rfl
      (EarlySerializeReturn.output_spec input rho hn hz)
  · let rho := J2Raw.finishRest (J2End.endFrame s input.size) []
    have hc : rho.length ≤ 20 := by simp [rho, J2Raw.finishRest]
    have gm := J2Loop.gasSteps_miss s [] moves input.size hn rfl h256 hz
    have hb := RecognitionAccumulator.allowed_bounds input.size hn
    have gf := EarlySerializeFallback.gasSteps input hfit hb.1
      s.memory (EarlySerializeReturn.prepared_memory_size input saved) rho hc
    have gfm : GasSteps (J2Moves.atState s 4838 rho)
        (StackTail.append (PaddingTrace.padFramed input) rho) := by
      simpa only [J2Moves.atState, EarlySerializeFallback.incoming, s,
        EarlySerializeReturn.prepared, RecognitionSelectorResult.copied,
        EarlySerializeReturn.beforeCopy, EarlySerializeReturn.base] using gf
    exact hgeneric rho hc (hentry.trans (gp.trans (gm.trans gfm)))

#print axioms of_returned
#print axioms from_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Correct
