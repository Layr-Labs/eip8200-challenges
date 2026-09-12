import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Entry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Correct

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 376)
    (href : KnownInputCompactState.referenceWord input ≠ KnownInputData.fullWord) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : verifyAcc input 376 = 0
  · have heq := (VerifierLogic.verifyAcc_zero_iff_eq input 376 hsize (by decide)).1 hz
    have hspec : spec input = Prefix256Finish.paddedDigest := by
      rw [heq, Prefix256Digest.spec_data_eq]
      rfl
    let trace := (Prefix256Entry.gasSteps_hit input hsize href).trans
      (VerifierCorrect.gasSteps_verify_hit 376 input (by decide) hsize hz)
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, VerifierFinish.vReturned, VerifierFinish.vStored,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 376) 0 32)) at heval
    rw [ShortPatternFinish.answerMemory_read, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      ((Prefix256Entry.gasSteps_hit input hsize href).trans
        (VerifierCorrect.gasSteps_verify_miss 376 input (by decide) hsize hz))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Correct
