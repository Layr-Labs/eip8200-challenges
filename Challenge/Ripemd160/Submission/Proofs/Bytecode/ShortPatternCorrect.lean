import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan56
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan120
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternCorrect
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

theorem correct56_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 2 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_56 input hsize).1 hz
    have hspec : spec input = ShortPatternDigest.paddedDigest56 := by
      rw [heq]
      exact ShortPatternDigest.spec_pattern56
    let trace := hentry.trans
      ((ShortPatternScan56.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 56 input (UInt256.ofNat (scalarAt 2))
          64 (scanAcc input 2) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 56) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 56 = ShortPatternDigest.paddedDigest56 := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((ShortPatternScan56.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 2))
            64 (scanAcc input 2) hz)))


theorem correct120_from_patternedEntry (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 120)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hz : scanAcc input 4 = 0
  · have heq := (ShortPatternLogic.scanAcc_zero_iff_eq_120 input hsize).1 hz
    have hspec : spec input = ShortPatternDigest.paddedDigest120 := by
      rw [heq]
      exact ShortPatternDigest.spec_pattern120
    let trace := hentry.trans
      ((ShortPatternScan120.gasSteps_scan input hsize).trans
        (ShortPatternFinish.gasSteps_finish_hit 120 input (UInt256.ofNat (scalarAt 4))
          128 (scanAcc input 4) hz (by decide) hsize))
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, ShortPatternFinish.returnedState,
        ShortPatternFinish.storedState, ShortPatternFinish.returnRest,
        stS, initialState, State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas (initialState submissionBytecode input 0) gas)
      (.returned (MachineState.readPadded (ShortPatternFinish.answerMemory 120) 0 32)) at heval
    have hdigest : ShortPatternFinish.paddedDigest 120 = ShortPatternDigest.paddedDigest120 := rfl
    rw [ShortPatternFinish.answerMemory_read, hdigest, ← hspec] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit
      (hentry.trans
        ((ShortPatternScan120.gasSteps_scan input hsize).trans
          (ShortPatternFinish.gasSteps_miss input (UInt256.ofNat (scalarAt 4))
            128 (scanAcc input 4) hz)))


#print axioms correct56_from_patternedEntry
#print axioms correct120_from_patternedEntry

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternCorrect
