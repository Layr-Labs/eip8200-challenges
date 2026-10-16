import Challenge.Ripemd160.Submission.Proofs.Bytecode.GasCost
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionEntryPrelude
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralScanV2
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

theorem from_entry (input : ByteArray)
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
  have e : DirectLiteralScanV2.Env s := ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩
  have gprepare := EarlySerializeReturn.gasSteps_prepare input saved (by simp [saved])
  have gp : GasSteps (PatternedScan.patternedEntry input)
      (J2Moves.atState s 4804 saved) := by
    exact GasSteps.cast gprepare rfl (EarlySerializeReturn.prepared_atState input saved)
  have gs := DirectLiteralScanV2.gasSteps_scan s e saved (by simp [saved]) hn
  have gs' : GasSteps (J2Moves.atState s 4804 saved)
      (J2Moves.atState s
        (if (DirectLiteralModel.result input input.size).toNat = 0 then 6109 else 4565) saved) := gs
  by_cases hz : (DirectLiteralModel.result input input.size).toNat = 0
  · rw [if_pos hz] at gs'
    have hzword : DirectLiteralModel.result input input.size = 0 := by
      apply Word.word_ext
      exact hz
    have heq := (DirectLiteralModel.result_zero_iff input input.size hn rfl).mp hzword
    have hold := (J2Accumulator.resultAcc_zero_iff input input.size hn rfl).mpr heq
    have gr := EarlySerializeReturn.gasSteps_return input saved saved (by simp [saved])
    have trace : GasSteps (initialState submissionBytecode input 0)
        (EarlySerializeReturn.output input saved) := hentry.trans (gp.trans (gs'.trans gr))
    exact of_returned input _ trace (EarlySerializeReturn.output_halt input saved) rfl
      (EarlySerializeReturn.output_spec input saved hn hold)
  · rw [if_neg hz] at gs'
    have hb := RecognitionAccumulator.allowed_bounds input.size hn
    have gf := EarlySerializeFallback.gasSteps input hfit hb.1
      s.memory (EarlySerializeReturn.prepared_memory_size input saved) saved (by simp [saved])
    have gfm : GasSteps (J2Moves.atState s 4565 saved)
        (StackTail.append (PaddingTrace.padFramed input) saved) := by
      simpa only [J2Moves.atState, EarlySerializeFallback.incoming, s,
        EarlySerializeReturn.prepared, RecognitionSelectorResult.copied,
        EarlySerializeReturn.beforeCopy, EarlySerializeReturn.base] using gf
    exact hgeneric saved (by simp [saved]) (hentry.trans (gp.trans (gs'.trans gfm)))

#print axioms of_returned
#print axioms from_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Correct
