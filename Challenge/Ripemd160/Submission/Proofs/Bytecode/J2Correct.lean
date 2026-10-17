import Challenge.Ripemd160.Submission.Proofs.Bytecode.GasCost
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionEntryPrelude
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseLiteralScan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseSerializeReturn
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

theorem from_prepared (input : ByteArray)
    (hn : RecognitionAccumulator.Allowed input.size)
    (hne : input.size ≠ 1000)
    (hfit : CalldataFits input)
    (hentry : GasSteps (initialState submissionBytecode input 0) (ReverseSerializeReturn.prepared input (PatternedScan.entryRho input.size)))
    (hgeneric : ∀ rho : List UInt256, rho.length ≤ 20 →
      GasSteps (initialState submissionBytecode input 0)
        (StackTail.append (PaddingTrace.padFramed input) rho) →
      ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
        Eval (initialState submissionBytecode input gas) (.returned (spec input))) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let saved : List UInt256 := PatternedScan.entryRho input.size
  have hsaved : saved.length ≤ 1 := PatternedScan.entryRho_length input.size
  let s := ReverseSerializeReturn.prepared input saved
  have e : ReverseLiteralScan.Env s := ⟨rfl, rfl, rfl, rfl, deployAddress_not_precompile⟩
  obtain ⟨i, hi⟩ := ReverseLiteralScan.allowed_index input.size hn hne
  have gp : GasSteps (ReverseSerializeReturn.prepared input saved)
      (J2Moves.atState s (ReverseLiteralScan.tailPC i) saved) := by
    rw [← ReverseSerializeReturn.prepared_atState input saved i hi.symm]
    exact GasSteps.refl _
  have gs := ReverseLiteralScan.gasSteps_for s e saved (by omega) i hi.symm
  have gs' : GasSteps (J2Moves.atState s (ReverseLiteralScan.tailPC i) saved)
      (J2Moves.atState s
        (if (ZeroTailModel.result input input.size).toNat = 0 then ReverseLiteralScan.returnPC i else 4785) saved) := gs
  by_cases hz : (ZeroTailModel.result input input.size).toNat = 0
  · rw [if_pos hz] at gs'
    have hzword : ZeroTailModel.result input input.size = 0 := by
      apply Word.word_ext
      exact hz
    have heq := (ZeroTailModel.result_zero_iff input input.size hn rfl).mp hzword
    have hold := (J2Accumulator.resultAcc_zero_iff input input.size hn rfl).mpr heq
    have gr := ReverseSerializeReturn.gasSteps_return input saved saved (by omega) i
    have trace : GasSteps (initialState submissionBytecode input 0)
        (ReverseSerializeReturn.output input saved i) := hentry.trans (gp.trans (gs'.trans gr))
    exact of_returned input _ trace (ReverseSerializeReturn.output_halt input saved i) rfl
      (ReverseSerializeReturn.output_spec input saved i hn hold)
  · rw [if_neg hz] at gs'
    have hb := RecognitionAccumulator.allowed_bounds input.size hn
    have gf := EarlySerializeFallback.gasSteps input hfit hb.1
      s.memory (ReverseSerializeReturn.prepared_memory_size input saved) saved (by omega)
    have gfm : GasSteps (J2Moves.atState s 4785 saved)
        (StackTail.append (PaddingTrace.padFramed input) saved) := by
      simpa only [J2Moves.atState, EarlySerializeFallback.incoming, s,
        ReverseSerializeReturn.prepared, ReverseSerializeReturn.base] using gf
    exact hgeneric saved (by omega) (hentry.trans (gp.trans (gs'.trans gfm)))

theorem from_entry (input : ByteArray)
    (hn : RecognitionAccumulator.Allowed input.size)
    (hne : input.size ≠ 1000)
    (hfit : CalldataFits input)
    (hentry : GasSteps (initialState submissionBytecode input 0) (PatternedScan.patternedEntry input))
    (hgeneric : ∀ rho : List UInt256, rho.length ≤ 20 →
      GasSteps (initialState submissionBytecode input 0)
        (StackTail.append (PaddingTrace.padFramed input) rho) →
      ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
        Eval (initialState submissionBytecode input gas) (.returned (spec input))) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  obtain ⟨i, hi⟩ := ReverseLiteralScan.allowed_index input.size hn hne
  have gp := ReverseSerializeReturn.gasSteps_prepare_loaded input (PatternedScan.entryRho input.size)
    (by have h := PatternedScan.entryRho_length input.size; omega) i hi.symm
  exact from_prepared input hn hne hfit (hentry.trans gp) hgeneric

#print axioms of_returned
#print axioms from_prepared
#print axioms from_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Correct
