import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Scan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned63Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Correct

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

theorem correct_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 63)    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 2 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_63 input hsize).1 hz
    have hspec : spec input = Patterned63Digest.paddedDigest := by
      rw [heq]
      exact Patterned63Digest.spec_data_eq
    let trace := hentry.trans
      ((Patterned128Scan.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 63 input (UInt256.ofNat (scalarAt 2))
          64 (scanAcc input 2) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 63) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 63 = Patterned63Digest.paddedDigest := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((Patterned128Scan.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 2))
            64 (scanAcc input 2) hz)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Correct
